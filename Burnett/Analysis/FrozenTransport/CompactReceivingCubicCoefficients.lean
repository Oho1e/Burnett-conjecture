import Burnett.Analysis.TransportWard.MetricVariation
import Burnett.Analysis.Microlocal.PhysicalDensity
import Burnett.Geometry.MaximalChart.MetricCoordinates
import Burnett.Analysis.FrozenTransport.CubicCoefficientFunctional

set_option autoImplicit false
set_option maxRecDepth 5700
set_option maxHeartbeats 9700000
noncomputable section

namespace Burnett.C02

open Set Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.Geometry Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.InverseField (continuousOn_matrixInverse)
open Burnett.Geometry.MaximalChart Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ContDiff Manifold Topology

private def orderedTensorBasis (k : OrderedPair) : Mat := Matrix.single k.1 k.2 1

private def coordinateDerivativeBasis (a : Index) : Cov := Pi.single a 1

/-- Polarization of the actual density-weighted kinetic coefficient in the
ordered tensor coordinates. The undifferentiated metric leg is last. -/
def frozenActionCubicLinear (G : Mat) (k : EnergyIndex OrderedPair) (l : OrderedPair) : ℝ :=
  principalLeg G (orderedTensorBasis l)
    (planeJet (coordinateDerivativeBasis k.1.1) (orderedTensorBasis k.2.1))
    (planeJet (coordinateDerivativeBasis k.1.2) (orderedTensorBasis k.2.2))

/-- Coefficient of the first-derivative term after integrating the two
differentiated test placements by parts, in A02's twice-imaginary convention. -/
def frozenActionCubicQuadratic (G : Mat) (a d : Index) (i j k : OrderedPair) : ℝ :=
  frozenActionCubicLinear G ((a,d),(k,j)) i - (1 / 2 : ℝ) * frozenActionCubicLinear G ((a,d),(i,j)) k

theorem frozenActionCubicLinear_symmetry (G : Mat) (a d : Index) (i j l : OrderedPair) :
    frozenActionCubicLinear G ((a,d),(i,j)) l = frozenActionCubicLinear G ((d,a),(j,i)) l :=
  principalLeg_comm G _ _ _

theorem frozenActionCubicLinear_derivative (G : Mat) (hG : Matrix.det G ≠ 0)
    (k : EnergyIndex OrderedPair) (l : OrderedPair) :
    frozenActionCubicLinear G k l =
      deriv (fun t : ℝ => metricKineticCoefficient (G + t • orderedTensorBasis l)
        (planeJet (coordinateDerivativeBasis k.1.1) (orderedTensorBasis k.2.1))
        (planeJet (coordinateDerivativeBasis k.1.2) (orderedTensorBasis k.2.2))) 0 :=
  (hasDerivAt_metricKineticCoefficient_path G _ hG _ _).deriv.symm

private theorem continuousOn_principalLeg_of_metric {X : Type*} [TopologicalSpace X]
    (G : X → Mat) (K : Set X) (hG : ContinuousOn G K) (hn : ∀ x ∈ K, Matrix.det (G x) ≠ 0)
    (H : Mat) (Y Z : Jet) : ContinuousOn (fun x => principalLeg (G x) H Y Z) K := by
  have hInv : ContinuousOn (fun x => inverseMatrix (G x)) K := continuousOn_matrixInverse G K hG hn
  have hI (a b : Index) : ContinuousOn (fun x => inverseMatrix (G x) a b) K :=
    continuousOn_pi.mp (continuousOn_pi.mp hInv a) b
  have hD : ContinuousOn (fun x => metricDensity (G x)) K :=
    Real.continuous_sqrt.comp_continuousOn (continuous_abs.comp_continuousOn
      ((continuous_id : Continuous (fun g : Mat => g)).matrix_det.comp_continuousOn hG))
  have hV (a b : Index) : ContinuousOn (fun x => inverseVariation (G x) H a b) K := by
    simp only [inverseVariation_apply]
    refine ContinuousOn.neg (continuousOn_finset_sum Finset.univ fun i _ => continuousOn_finset_sum Finset.univ fun j _ => ?_)
    exact ((hI a i).mul continuousOn_const).mul (hI j b)
  have hTr : ContinuousOn (fun x => traceVariation (G x) H) K := by
    simp only [traceVariation, Matrix.trace, Matrix.diag, Matrix.mul_apply]
    exact continuousOn_finset_sum Finset.univ fun i _ => continuousOn_finset_sum Finset.univ fun j _ => continuousOn_const.mul (hI j i)
  have hAV (Q : Jet) : ContinuousOn (fun x => actionDensityVariation (G x) H Q) K := by
    have hΓ (a b c : Index) : ContinuousOn (fun x => christoffel (inverseMatrix (G x)) Q a b c) K := by
      unfold christoffel
      exact continuousOn_finset_sum Finset.univ fun d _ => (hI a d).mul continuousOn_const
    have hΓV (a b c : Index) : ContinuousOn (fun x => connectionVariation (G x) H Q a b c) K := by
      unfold connectionVariation christoffel
      exact continuousOn_finset_sum Finset.univ fun d _ => (hV a d).mul continuousOn_const
    have hQD (b c : Index) : ContinuousOn (fun x => quadraticDifference (christoffel (inverseMatrix (G x)) Q) b c) K := by
      unfold quadraticDifference
      exact continuousOn_finset_sum Finset.univ fun a _ => continuousOn_finset_sum Finset.univ fun e _ =>
        ((hΓ a a e).mul (hΓ e b c)).sub ((hΓ a c e).mul (hΓ e b a))
    have hDC (b c : Index) : ContinuousOn (fun x =>
        quadraticConnectionVariation (christoffel (inverseMatrix (G x)) Q) (connectionVariation (G x) H Q) b c) K := by
      unfold quadraticConnectionVariation
      exact continuousOn_finset_sum Finset.univ fun a _ => continuousOn_finset_sum Finset.univ fun e _ =>
        (((hΓV a a e).mul (hΓ e b c)).add ((hΓ a a e).mul (hΓV e b c))).sub
          (((hΓV a c e).mul (hΓ e b a)).add ((hΓ a c e).mul (hΓV e b a)))
    have hQ : ContinuousOn (fun x => quadraticAction (inverseMatrix (G x)) Q) K := by
      unfold quadraticAction
      exact continuousOn_finset_sum Finset.univ fun b _ => continuousOn_finset_sum Finset.univ fun c _ => (hI b c).mul (hQD b c)
    have hQV : ContinuousOn (fun x => quadraticActionVariation (G x) H Q) K := by
      unfold quadraticActionVariation
      exact continuousOn_finset_sum Finset.univ fun b _ => continuousOn_finset_sum Finset.univ fun c _ =>
        ((hV b c).mul (hQD b c)).add ((hI b c).mul (hDC b c))
    unfold actionDensityVariation
    exact (((hD.div continuousOn_const fun _ _ => by norm_num).mul hTr).mul hQ).add (hD.mul hQV)
  unfold principalLeg
  exact ((hAV (Y + Z)).sub (hAV Y)).sub (hAV Z)

theorem continuousOn_frozenActionCubicLinear {X : Type*} [TopologicalSpace X]
    (G : X → Mat) (K : Set X) (hG : ContinuousOn G K) (hn : ∀ x ∈ K, Matrix.det (G x) ≠ 0)
    (k : EnergyIndex OrderedPair) (l : OrderedPair) :
    ContinuousOn (fun x => frozenActionCubicLinear (G x) k l) K :=
  continuousOn_principalLeg_of_metric G K hG hn _ _ _

theorem continuousOn_frozenActionCubicQuadratic {X : Type*} [TopologicalSpace X]
    (G : X → Mat) (K : Set X) (hG : ContinuousOn G K) (hn : ∀ x ∈ K, Matrix.det (G x) ≠ 0)
    (a d : Index) (i j k : OrderedPair) :
    ContinuousOn (fun x => frozenActionCubicQuadratic (G x) a d i j k) K :=
  (continuousOn_frozenActionCubicLinear G K hG hn ((a,d),(k,j)) i).sub
    (continuousOn_const.mul (continuousOn_frozenActionCubicLinear G K hG hn ((a,d),(i,j)) k))

private theorem exists_compact_finite_family_abs_bound {X I : Type*} [TopologicalSpace X] [Fintype I]
    (K : Set X) (hK : IsCompact K) (f : I → X → ℝ) (hf : ∀ i, ContinuousOn (f i) K) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ i x, x ∈ K → |f i x| ≤ B := by
  classical
  choose A hA using fun i => hK.exists_bound_of_continuousOn (hf i)
  let B := ∑ i, max 0 (A i)
  refine ⟨B, Finset.sum_nonneg (fun _ _ => le_max_left _ _), fun i x hx => ?_⟩
  have hdom : A i ≤ B := (le_max_right _ _).trans
    (Finset.single_le_sum (fun j _ => le_max_left 0 (A j)) (Finset.mem_univ i))
  simpa only [Real.norm_eq_abs] using (hA i x hx).trans hdom

/-- A compact chart has a common bound on all frozen coordinate coefficients.
The bound is independent of the lattice scale, the patch index, and the
subsequence. -/
theorem exists_frozenActionCubicCoefficient_box {X : Type*} [TopologicalSpace X]
    (G : X → Mat) (K : Set X) (hK : IsCompact K) (hG : ContinuousOn G K)
    (hn : ∀ x ∈ K, Matrix.det (G x) ≠ 0) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ K,
      (∀ k l, |frozenActionCubicLinear (G x) k l| ≤ B) ∧
      (∀ a d i j k, |frozenActionCubicQuadratic (G x) a d i j k| ≤ B) := by
  obtain ⟨L, hL, hLin⟩ := exists_compact_finite_family_abs_bound K hK
    (fun k : CubicLinearIndex OrderedPair => fun x => frozenActionCubicLinear (G x) k.1 k.2)
    (fun k => continuousOn_frozenActionCubicLinear G K hG hn k.1 k.2)
  obtain ⟨Q, hQ, hQuad⟩ := exists_compact_finite_family_abs_bound K hK
    (fun k : CubicQuadraticIndex OrderedPair => fun x =>
      frozenActionCubicQuadratic (G x) k.2.1.1 k.2.2.1 k.2.1.2 k.2.2.2 k.1)
    (fun k => continuousOn_frozenActionCubicQuadratic G K hG hn k.2.1.1 k.2.2.1 k.2.1.2 k.2.2.2 k.1)
  exact ⟨L + Q, add_nonneg hL hQ, fun x hx => ⟨
    fun k l => (hLin (k,l) x hx).trans (le_add_of_nonneg_right hQ),
    fun a d i j k => (hQuad (k, ((a,i),(d,j))) x hx).trans (le_add_of_nonneg_left hL)⟩⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

theorem exists_receivingFrozenCubicCoefficient_box
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ c.chart.target) :
    let G (x : E) := metricComponents (fixedForm B c) x
    ∃ M₀ : ℝ, 0 ≤ M₀ ∧ ∀ x ∈ K,
      (∀ k l, |frozenActionCubicLinear (G x) k l| ≤ M₀) ∧
      (∀ a d i j k, |frozenActionCubicQuadratic (G x) a d i j k| ≤ M₀) := by
  intro G
  have hG : ContinuousOn G K :=
    continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun d =>
      (fixedForm_components_smooth B hB c a d).continuousOn.mono hKU
  exact exists_frozenActionCubicCoefficient_box G K hK hG
    (fun _ hx => fixedForm_det_ne_zero B hn c (hKU hx))

end Burnett.C02
