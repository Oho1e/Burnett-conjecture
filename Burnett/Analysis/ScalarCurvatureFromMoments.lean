import Burnett.Geometry.IntrinsicScalarEinstein
import Burnett.Analysis.MeasureWeakRicci
import Mathlib.Geometry.Manifold.BumpFunction

/-! Trace the Ricci moments on the actual null shell and recover Einstein moments. -/

set_option autoImplicit false
set_option maxHeartbeats 560000
noncomputable section

namespace Burnett.Analysis.ScalarCurvatureFromMoments

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open ContravariantTensor IntrinsicScalarEinstein UnitNullCompactness InverseField
open BackgroundConnection CurvatureDifference
open Burnett.Analysis.LocalWeakRicciIdentification (coordinateRicci_component_smoothOn)
open scoped BigOperators ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

omit [BorelSpace M] [SecondCountableTopology M] in
private theorem eq_zero_of_all_smooth_tests (V : Measure M) [V.IsOpenPosMeasure]
    (f : M → ℝ) (hf : Continuous f)
    (hTest : ∀ φ : M → ℝ, ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ →
      Integrable (fun x => φ x * f x) V ∧ (∫ x, φ x * f x ∂V) = 0) : ∀ x, f x = 0 := by
  have nonpos (g : M → ℝ) (hg : Continuous g)
      (ht : ∀ φ : M → ℝ, ContMDiff Model 𝓘(ℝ) ∞ φ → HasCompactSupport φ →
        Integrable (fun x => φ x * g x) V ∧ (∫ x, φ x * g x ∂V) = 0) (x : M) : g x ≤ 0 := by
    apply le_of_not_gt
    intro hx
    have hU : IsOpen {y | 0 < g y} := isOpen_lt continuous_const hg
    obtain ⟨b, _, hs⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) x).mem_iff.mp (hU.mem_nhds hx)
    obtain ⟨hInt, hEq⟩ := ht b b.contMDiff b.hasCompactSupport
    have hPos (y : M) : 0 ≤ b y * g y := by
      by_cases hy : y ∈ tsupport b
      · exact mul_nonneg b.nonneg ((hs hy : 0 < g y).le)
      · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul]
    have hae := (integral_eq_zero_iff_of_nonneg hPos hInt).mp hEq
    have hzero := congrFun (V.eq_of_ae_eq hae (b.contMDiff.continuous.mul hg) continuous_const) x
    have hbx : b x = 1 := b.eventuallyEq_one.eq_of_nhds
    exact hx.ne' (by simpa only [hbx, one_mul, Pi.zero_apply] using hzero)
  intro x
  refine le_antisymm (nonpos f hf hTest x) (neg_nonpos.mp (nonpos (fun y => -f y) hf.neg ?_ x))
  intro φ hφ hc
  obtain ⟨hi, heq⟩ := hTest φ hφ hc
  exact ⟨by simpa only [mul_neg] using hi.neg, by simp only [mul_neg, integral_neg, heq, neg_zero]⟩

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
theorem continuous_intrinsicScalar (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B) : Continuous (intrinsicScalar B hn) := by
  apply continuous_iff_continuousAt.mpr
  intro c
  let e := chartAt CoordinateSpace c
  have hG (i j : Index) : ContinuousOn (fun y =>
      matrixInverse (metricComponents (coordinateBilinear B c) y) i j) e.target :=
    (SmoothMetricConnection.contDiffOn_matrixInverse (metricComponents (coordinateBilinear B c)) e.target
      (ManifoldBilinear.contDiffOn_metricComponents B hB c)
      (fun _ hy => ManifoldVolumeRegularity.coordinate_det_ne_zero B hn c hy) i j).continuousOn
  have hR (i j : Index) := (coordinateRicci_component_smoothOn B hB hn c i j).continuousOn
  have hScalar : ContinuousOn (chartScalarCurvature B c) e.target := by
    unfold chartScalarCurvature metricTrace
    exact continuousOn_finset_sum Finset.univ (fun i _ =>
      continuousOn_finset_sum Finset.univ (fun j _ => (hG i j).mul (hR i j)))
  exact ((hScalar.comp e.continuousOn e.mapsTo).congr
    (fun x hx => intrinsicScalar_chart B hB hs hn c x hx)).continuousAt
      (e.open_source.mem_nhds (mem_chart_source CoordinateSpace c))

omit [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] in
private theorem isTensorTest_smul_inverseMetric (B : Field (M := M)) (hB : IsSmooth B)
    (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (φ : M → ℝ) (hφ : ContMDiff Model 𝓘(ℝ) ∞ φ) (hc : HasCompactSupport φ) :
    IsTensorTest (fun x => φ x • inverseMetricTensor B hn x) := by
  let Q (x : M) := φ x • inverseMetricTensor B hn x
  change IsTensorTest Q
  refine ⟨?_, ?_, ?_⟩
  · intro x
    constructor
    intro u v
    change φ x * inverseMetricTensor B hn x u v = φ x * inverseMetricTensor B hn x v u
    rw [(inverseMetricTensor_isSymmetric B hn hs x).eq u v]
  · change IsCompact (closure {x | Q x ≠ 0})
    apply hc.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx
    change φ x ≠ 0
    intro hzero
    exact hx (by simp [Q, hzero])
  · intro c i j
    let e := chartAt CoordinateSpace c
    have hφc : ContDiffOn ℝ ∞ (φ ∘ e.symm) e.target :=
      (hφ.contMDiffOn.comp contMDiffOn_chart_symm e.symm.mapsTo).contDiffOn
    have hG := SmoothMetricConnection.contDiffOn_matrixInverse
      (metricComponents (coordinateBilinear B c)) e.target
      (ManifoldBilinear.contDiffOn_metricComponents B hB c)
      (fun _ hy => ManifoldVolumeRegularity.coordinate_det_ne_zero B hn c hy) i j
    refine (hφc.mul hG).congr ?_
    intro y hy
    have hInv := inverseMetricTensor_components B hn hs c (e.symm y) (e.symm_mapsTo hy) i j
    have hey : chartAt CoordinateSpace c (e.symm y) = y := e.right_inv hy
    rw [hey] at hInv
    change φ (e.symm y) * contravariantComponents (inverseMetricTensor B hn) c y i j = _
    simp only [hInv, Function.comp_apply]

variable [MeasurableSpace (CotangentBundle M)]

/-- The Ricci moment identity for every actual smooth compact symmetric tensor test. -/
def HasRicciMoments (B : Field (M := M)) (μ : Measure (CotangentBundle M)) : Prop :=
  ∀ Q : ContravariantTwoTensor M, IsTensorTest Q →
    Integrable (intrinsicTensorBase B Q) (ManifoldVolume.geometricMeasure B) ∧
    Integrable (intrinsicTensorPhase Q) μ ∧
    (∫ x, intrinsicTensorBase B Q x ∂ManifoldVolume.geometricMeasure B) =
      ∫ p, intrinsicTensorPhase Q p ∂μ

/-- Testing with a compact scalar multiple of the inverse metric gives
pointwise scalar curvature zero when the same Ricci moment measure is null. -/
theorem scalarCurvature_eq_zero_of_null_RicciMoments
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (μ : Measure (CotangentBundle M)) (hNull : μ (cotangentUnitNull r B hn)ᶜ = 0)
    (hMom : HasRicciMoments B μ) : ∀ x, intrinsicScalar B hn x = 0 := by
  let V := ManifoldVolume.geometricMeasure B
  letI : V.IsOpenPosMeasure := ManifoldVolumeRegularity.geometricMeasure_isOpenPosMeasure B hB hn
  apply eq_zero_of_all_smooth_tests V (intrinsicScalar B hn) (continuous_intrinsicScalar B hB hs hn)
  intro φ hφ hc
  let Q (x : M) := φ x • inverseMetricTensor B hn x
  obtain ⟨hBase, _, hEq⟩ := hMom Q (isTensorTest_smul_inverseMetric B hB hs hn φ hφ hc)
  have hBaseEq (x : M) : intrinsicTensorBase B Q x = φ x * intrinsicScalar B hn x := by
    have hx := mem_chart_source CoordinateSpace x
    rw [intrinsicScalar, intrinsicTensorBase_eq_components B hB hs hn Q x x hx,
      intrinsicTensorBase_eq_components B hB hs hn (inverseMetricTensor B hn) x x hx,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hComp : contravariantComponents Q x (chartAt CoordinateSpace x x) i j =
        φ x * contravariantComponents (inverseMetricTensor B hn) x (chartAt CoordinateSpace x x) i j := by
      rw [contravariantComponents_chart Q x x hx, contravariantComponents_chart (inverseMetricTensor B hn) x x hx]
      rfl
    rw [hComp, mul_assoc]
  have hPhaseEq (p : CotangentBundle M) : intrinsicTensorPhase Q p = φ p.proj * dualEnergy B hn p := by
    change φ p.proj * intrinsicTensorPhase (inverseMetricTensor B hn) p = _
    rw [intrinsicTensorPhase_inverseMetric B hn hs p]
  have hNullAE : ∀ᵐ p ∂μ, p ∈ cotangentUnitNull r B hn := by
    rw [ae_iff]
    exact hNull
  have hzero : (∫ p, intrinsicTensorPhase Q p ∂μ) = 0 := by
    rw [← integral_zero]
    apply integral_congr_ae
    filter_upwards [hNullAE] with p hp
    change _ ∧ dualEnergy B hn p = 0 at hp
    rw [hPhaseEq, hp.2, mul_zero]
  have hBaseFun : intrinsicTensorBase B Q = fun x => φ x * intrinsicScalar B hn x := funext hBaseEq
  rw [hBaseFun] at hBase hEq
  exact ⟨hBase, hEq.trans hzero⟩

/-- The same null measure gives the Einstein moments after the trace vanishes. -/
theorem scalarFlat_and_EinsteinMoments_of_null_RicciMoments
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (μ : Measure (CotangentBundle M)) (hNull : μ (cotangentUnitNull r B hn)ᶜ = 0)
    (hMom : HasRicciMoments B μ) :
    (∀ x, intrinsicScalar B hn x = 0) ∧
      ∀ Q : ContravariantTwoTensor M, IsTensorTest Q →
        Integrable (einsteinPair B hn Q) (ManifoldVolume.geometricMeasure B) ∧
        Integrable (intrinsicTensorPhase Q) μ ∧
        (∫ x, einsteinPair B hn Q x ∂ManifoldVolume.geometricMeasure B) =
          ∫ p, intrinsicTensorPhase Q p ∂μ := by
  have hZero := scalarCurvature_eq_zero_of_null_RicciMoments r B hB hs hn μ hNull hMom
  refine ⟨hZero, fun Q hQ => ?_⟩
  have hEinstein : einsteinPair B hn Q = intrinsicTensorBase B Q :=
    funext fun x => einsteinPair_eq_intrinsicTensorBase_of_scalar_zero B hn Q x (hZero x)
  rw [hEinstein]
  exact hMom Q hQ

end Burnett.Analysis.ScalarCurvatureFromMoments
