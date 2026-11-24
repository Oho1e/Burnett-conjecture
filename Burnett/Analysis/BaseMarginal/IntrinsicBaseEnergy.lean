import Burnett.Analysis.Microlocal.Overlap.CosphereEinsteinMoments

/-! Trace the actual Einstein tests with the inverse auxiliary metric. -/
set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set MeasureTheory Filter Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricTransition ContravariantTensor
open IntrinsicScalarEinstein UnitNullCompactness InverseField
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)
open Burnett.Analysis.LocalWeakRicciIdentification (coordinateRicci_component_smoothOn)
open scoped ContDiff Manifold Topology ENNReal

open private isTensorTest_smul_inverseMetric from Burnett.Analysis.ScalarCurvatureFromMoments

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The paper's scalar density e_r is the auxiliary trace of the actual Einstein tensor. -/
def auxiliaryEinsteinDensity (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B) : M → ℝ :=
  einsteinPair B hn (inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r))

variable [T2Space M]

theorem contMDiff_auxiliaryEinsteinDensity (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B) :
    ContMDiff Model 𝓘(ℝ) ∞ (auxiliaryEinsteinDensity r B hn) := by
  intro c
  let e := chartAt CoordinateSpace c
  let inv (A : Field (M := M)) (y : CoordinateSpace) := matrixInverse (metricComponents (coordinateBilinear A c) y)
  have hInv (A : Field (M := M)) (hA : IsSmooth A) (hnA : IsNondegenerate A) (i j : Index) :
      ContDiffOn ℝ ∞ (fun y => inv A y i j) e.target :=
    SmoothMetricConnection.contDiffOn_matrixInverse _ e.target (contDiffOn_metricComponents A hA c)
      (fun _ hy => ManifoldVolumeRegularity.coordinate_det_ne_zero A hnA c hy) i j
  have hRicci (i j : Index) := coordinateRicci_component_smoothOn B hB hn c i j
  have hScalar : ContDiffOn ℝ ∞ (chartScalarCurvature B c) e.target := by
    unfold chartScalarCurvature metricTrace
    exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ => (hInv B hB hn i j).mul (hRicci i j)))
  have hEinstein (i j : Index) : ContDiffOn ℝ ∞ (fun y => chartEinstein B c y i j) e.target :=
    (hRicci i j).sub ((hScalar.div_const 2).mul (contDiffOn_metricComponents B hB c i j))
  let F (y : CoordinateSpace) := ∑ i, ∑ j, inv r.inner y i j * chartEinstein B c y i j
  have hF : ContDiffOn ℝ ∞ F e.target :=
    ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (hInv r.inner (isSmooth_inner r) (GlobalLeviCivita.inner_nondegenerate r) i j).mul (hEinstein i j)))
  have hComp := hF.contMDiffOn.comp (contMDiffOn_chart (I := Model) (x := c)) e.mapsTo
  have hS : ContMDiffOn Model 𝓘(ℝ) ∞ (auxiliaryEinsteinDensity r B hn) e.source := by
    refine hComp.congr fun x hx => ?_
    rw [auxiliaryEinsteinDensity, einsteinPair_eq_components B hB hs hn _ c x hx]
    simp only [F, inv, Function.comp_apply,
      inverseMetricTensor_components r.inner (GlobalLeviCivita.inner_nondegenerate r) r.symm c x hx]
  exact hS.contMDiffAt (e.open_source.mem_nhds (mem_chart_source CoordinateSpace c))

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

omit [T2Space M] in
/-- Scalar compact tests of the projected measure are exactly tests of e_r against dV. -/
theorem auxiliaryEinsteinDensity_tests_on_original_measure (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (Cosphere r)) (hMom : HasCosphereEinsteinMoments r B hn μ)
    (φ : M → ℝ) (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x * auxiliaryEinsteinDensity r B hn x) (ManifoldVolume.geometricMeasure B) ∧
    Integrable (fun p : Cosphere r => φ (projection p)) μ ∧
    (∫ x, φ x * auxiliaryEinsteinDensity r B hn x ∂ManifoldVolume.geometricMeasure B) =
      ∫ p : Cosphere r, φ (projection p) ∂μ := by
  let hnR := GlobalLeviCivita.inner_nondegenerate r
  let R := inverseMetricTensor r.inner hnR
  let Q : ContravariantTwoTensor M := fun x => φ x • R x
  obtain ⟨hBase, hPhase, hEq⟩ := hMom Q
    (isTensorTest_smul_inverseMetric r.inner (isSmooth_inner r) r.symm hnR φ hφ hc)
  have heBase (x : M) : einsteinPair B hn Q x = φ x * auxiliaryEinsteinDensity r B hn x := by
    let b := tensorTangentBasis x x (mem_chart_source CoordinateSpace x)
    rw [auxiliaryEinsteinDensity, einsteinPair, einsteinPair, contractAt_eq_sum x b, contractAt_eq_sum x b,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact mul_assoc _ _ _
  have hePhase (p : Cosphere r) : intrinsicTensorPhase Q p.val = φ (projection p) := by
    change φ (projection p) * intrinsicTensorPhase R p.val = _
    rw [intrinsicTensorPhase_inverseMetric r.inner hnR r.symm p.val, show dualEnergy r.inner hnR p.val = 1 from p.prop, mul_one]
  refine ⟨hBase.congr (Eventually.of_forall heBase), hPhase.congr (Eventually.of_forall hePhase), ?_⟩
  simpa only [heBase, hePhase] using hEq

/-- Positivity of the original physical measure gives pointwise nonnegativity of the smooth density. -/
theorem auxiliaryEinsteinDensity_nonneg_of_moments (r : Metric (M := M)) (B : Field (M := M))
    (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (μ : Measure (Cosphere r)) (hMom : HasCosphereEinsteinMoments r B hn μ) (x : M) :
    0 ≤ auxiliaryEinsteinDensity r B hn x := by
  by_contra! hx
  let V := ManifoldVolume.geometricMeasure B
  let h : M → ℝ := auxiliaryEinsteinDensity r B hn
  letI : V.IsOpenPosMeasure := ManifoldVolumeRegularity.geometricMeasure_isOpenPosMeasure B hB hn
  have hC : Continuous h := (contMDiff_auxiliaryEinsteinDensity r B hB hs hn).continuous
  have hU : IsOpen {y | h y < 0} := isOpen_lt hC continuous_const
  obtain ⟨b, _, hSub⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) x).mem_iff.mp (hU.mem_nhds hx)
  obtain ⟨hI, _, hTest⟩ := auxiliaryEinsteinDensity_tests_on_original_measure r B hn μ hMom b b.contMDiff b.hasCompactSupport
  have hF (y : M) : 0 ≤ -(b y * h y) := by
    by_cases hy : y ∈ tsupport b
    · exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos b.nonneg ((hSub hy : h y < 0).le))
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, neg_zero]
  have hVal : (∫ y, b y * h y ∂V) = 0 := by
    apply le_antisymm
    · apply neg_nonneg.mp
      rw [← integral_neg]
      exact integral_nonneg hF
    · rw [hTest]
      exact integral_nonneg fun _ => b.nonneg
  have hInt : (∫ y, -(b y * h y) ∂V) = 0 := by rw [integral_neg, hVal, neg_zero]
  have hae : (fun y => -(b y * h y)) =ᵐ[V] (fun _ => (0 : ℝ)) := (integral_eq_zero_iff_of_nonneg hF hI.neg).mp hInt
  have hz := congrFun (V.eq_of_ae_eq hae (b.contMDiff.continuous.mul hC).neg continuous_const) x
  have hbx : b x = 1 := b.eventuallyEq_one.eq_of_nhds
  exact hx.ne (by simpa only [hbx, one_mul, neg_eq_zero, Pi.zero_apply] using hz)

end Burnett.F08.IntrinsicBaseMarginal
