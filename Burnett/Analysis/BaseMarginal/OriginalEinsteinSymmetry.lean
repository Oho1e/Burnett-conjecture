import Burnett.Analysis.BaseMarginal.SmoothTests
import Burnett.Analysis.ScalarCurvatureFromMoments
import Burnett.Geometry.AuxiliaryAdmissibility

/-! Symmetry of the original Einstein tensor via the original weak Ricci identification. -/
set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 4700000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory Module Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference BackgroundConnection CurvatureDifference AuxiliaryConnection
open ManifoldMetric ManifoldBilinear ManifoldMetricSequence ManifoldMetricTransition
open ContravariantTensor IntrinsicScalarEinstein
open Burnett.Analysis.LocalWeakRicciIdentification
open Burnett.F08.ActualBaseMarginal (nonnegOn_of_smooth_test_integrals)
open scoped ContDiff Manifold Topology ENNReal

private theorem quadraticDifference_symmetric_of_torsionFree (C : Connection)
    (hC : ∀ a b d, C a b d = C a d b) (i j : Index) :
    quadraticDifference C i j = quadraticDifference C j i := by
  have hTrace : (∑ a : Index, ∑ e : Index, C a j e * C e i a) = ∑ a : Index, ∑ e : Index, C a i e * C e j a := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro e _
    exact mul_comm _ _
  simp only [quadraticDifference, Finset.sum_sub_distrib, hC _ i j, hTrace]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem linearConnection_torsionFree (B A : Field (M := M)) (hB : IsSymmetric B) (hA : IsSymmetric A)
    (c : M) (y : CoordinateSpace) (a i j : Index) :
    linearConnection (coordinateBilinear B c) (coordinateBilinear A c) y a i j =
      linearConnection (coordinateBilinear B c) (coordinateBilinear A c) y a j i := by
  let H (x : CoordinateSpace) := metricComponents (coordinateBilinear A c) x - metricComponents (coordinateBilinear B c) x
  have hH (x : CoordinateSpace) : IsSymmetricTensor (H x) := fun u v => by
    change metricComponents (coordinateBilinear A c) x u v - metricComponents (coordinateBilinear B c) x u v = _
    rw [show metricComponents (coordinateBilinear A c) x u v = metricComponents (coordinateBilinear A c) x v u from
      (coordinateBilinear_symmetric A hA c x).eq _ _,
      show metricComponents (coordinateBilinear B c) x u v = metricComponents (coordinateBilinear B c) x v u from
      (coordinateBilinear_symmetric B hB c x).eq _ _]
    rfl
  have hJet := coordinateJet_symmetric H y (Eventually.of_forall hH)
  unfold linearConnection auxiliaryPerturbationJet
  apply christoffel_torsion_free _ _ _ a i j
  intro d u v
  let Γ := computedConnection (coordinateBilinear B c) y
  change covariantJet Γ (H y) (coordinateJet H y) d u v = covariantJet Γ (H y) (coordinateJet H y) d v u
  unfold covariantJet
  rw [hJet d u v]
  have hSwap (k l : Index) : (∑ e, Γ e d k * H y e l) = ∑ e, Γ e d k * H y l e :=
    Finset.sum_congr rfl fun e _ => congrArg (Γ e d k * ·) (hH y e l)
  rw [hSwap u v, hSwap v u]
  ring

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem coordinateRicci_symmetric_of_originalVacuum
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) (i j : Index) :
    coordinateRicci (computedConnection (coordinateBilinear B c)) y i j =
      coordinateRicci (computedConnection (coordinateBilinear B c)) y j i := by
  let W := (chartAt CoordinateSpace c).target
  let v := ManifoldVolume.coordinateMeasure B c
  let R (x : CoordinateSpace) := coordinateRicci (computedConnection (coordinateBilinear B c)) x
  have hW : IsOpen W := (chartAt CoordinateSpace c).open_target
  have hOpen (U : Set CoordinateSpace) (hU : IsOpen U) (hSub : U ⊆ W) (hne : U.Nonempty) : v U ≠ 0 :=
    (LorentzVolume.coordinateMeasure_open_pos _ W hW (continuousOn_components B hB c)
      (fun x hx => ManifoldVolumeRegularity.coordinate_det_ne_zero B hnB c hx) hU hne hSub).ne'
  have hVac := IntrinsicRicciTrace.sequence_coordinateVacuum_of_intrinsic g hg hsG hnG hv c
  have hPos (a d : Index) : R y d a ≤ R y a d := by
    apply sub_nonneg.mp
    apply nonnegOn_of_smooth_test_integrals v hW (fun x => R x a d - R x d a)
      ((coordinateRicci_component_smoothOn B hB hnB c a d).sub
        (coordinateRicci_component_smoothOn B hB hnB c d a)).continuousOn hOpen _ _ y hy
    · intro ψ hψ hc hS
      obtain ⟨_, hI₁, _⟩ := vacuum_Ricci_coordinateMeasure_limit_of_original r B g hB hg hsB hsG
        hnB hnG hconv hb c hVac a d hψ hc hS
      obtain ⟨_, hI₂, _⟩ := vacuum_Ricci_coordinateMeasure_limit_of_original r B g hB hg hsB hsG
        hnB hnG hconv hb c hVac d a hψ hc hS
      simpa only [mul_sub] using hI₁.sub hI₂
    · intro ψ hψ hc hS _
      obtain ⟨_, hI₁, h₁⟩ := vacuum_Ricci_coordinateMeasure_limit_of_original r B g hB hg hsB hsG
        hnB hnG hconv hb c hVac a d hψ hc hS
      obtain ⟨_, hI₂, h₂⟩ := vacuum_Ricci_coordinateMeasure_limit_of_original r B g hB hg hsB hsG
        hnB hnG hconv hb c hVac d a hψ hc hS
      have hEq := tendsto_nhds_unique h₁ (h₂.congr (fun n => integral_congr_ae (Eventually.of_forall fun x => by
        rw [quadraticDifference_symmetric_of_torsionFree _ (linearConnection_torsionFree B (g n) hsB (hsG n) c x) d a])))
      apply le_of_eq
      simp only [mul_sub]
      rw [integral_sub hI₁ hI₂]
      exact (sub_eq_zero.mpr hEq).symm
  exact le_antisymm (hPos j i) (hPos i j)

theorem intrinsicEinstein_isSymm_of_originalVacuum
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (x : M) : (intrinsicEinstein B hnB x).IsSymm := by
  have hx : x ∈ (chartAt CoordinateSpace x).source := mem_chart_source CoordinateSpace x
  let b := tensorTangentBasis x x hx
  let E := intrinsicEinstein B hnB x
  have hEq : E = E.flip := by
    apply b.ext
    intro a
    apply b.ext
    intro d
    change E (b a) (b d) = E (b d) (b a)
    rw [intrinsicEinstein_components B hB hsB hnB x x hx, intrinsicEinstein_components B hB hsB hnB x x hx]
    unfold chartEinstein
    rw [coordinateRicci_symmetric_of_originalVacuum r B g hB hg hsB hsG hnB hnG hconv hb hv x
      ((chartAt CoordinateSpace x).mapsTo hx) a d]
    exact congrArg (fun z => _ - chartScalarCurvature B x (chartAt CoordinateSpace x x) / 2 * z)
      ((coordinateBilinear_symmetric B hsB x _).eq _ _)
  exact ⟨fun u v => LinearMap.congr_fun₂ hEq u v⟩

end Burnett.F08.IntrinsicBaseMarginal
