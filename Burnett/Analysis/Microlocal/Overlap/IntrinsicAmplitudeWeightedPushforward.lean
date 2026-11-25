import Burnett.Analysis.Microlocal.Overlap.OriginalAmplitudeAuxiliaryPair

/-! The weighted change of section for the amplitude covariance, tested
linearly in the actual fiber over the unchanged physical base. -/
set_option autoImplicit false
set_option maxRecDepth 4100
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Filter Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.CotangentAngularExtension (cotangentNorm cotangentNorm_sq)
open Burnett.Geometry.CotangentUnitNormalization (unitShell_punctured)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeFiber)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The old ray carries the square of its norm for the new auxiliary metric. -/
theorem cotangentAuxiliaryWeight_eq_ofReal_norm_sq_on_cosphere (r r' : Metric (M := M)) (p : Cosphere r) :
    cotangentAuxiliaryWeight r' p.val = ENNReal.ofReal (cotangentNorm r' p.val ^ 2) := by
  rw [cotangentAuxiliaryWeight, cotangentNorm_sq r' (unitShell_punctured r p.property)]

/-- Pull a ray-dependent functional back along the radial map, using the
actual equality of base points to keep its tensor argument in the same fiber. -/
def pullbackAmplitudeFiberTest (r r' : Metric (M := M))
    (L : ∀ p : Cosphere r', AmplitudeFiber (projection p) →ₗ[ℝ] ℂ)
    (p : Cosphere r) (v : AmplitudeFiber (projection p)) : ℂ :=
  L (renormalizeUnitCosphere r r' p)
    (cast (congrArg (fun x : M => AmplitudeFiber x)
      (renormalizeUnitCosphere_projection r r' p).symm) v)

omit [IsManifold Model ∞ M] in
private theorem apply_of_cast_eq_smul {x y : M} (h : y = x)
    (L : AmplitudeFiber y →ₗ[ℝ] ℂ) (v : AmplitudeFiber x) (w : AmplitudeFiber y) (a : ℝ)
    (hw : cast (congrArg (fun z : M => AmplitudeFiber z) h) w = a • v) :
    L w = a • L (cast (congrArg (fun z : M => AmplitudeFiber z) h.symm) v) := by
  subst y
  change w = a • v at hw
  change L w = a • L v
  rw [hw, map_smul]

/-- The weak form of the weighted pushforward of the actual tensor covariance.
All angular dependence of the fiber-linear test is retained, and integrability
on either side gives integrability on the other. -/
def HasIntrinsicAmplitudeWeightedPushforward (r r' : Metric (M := M))
    (A : IntrinsicAmplitudeCovariance r) (A' : IntrinsicAmplitudeCovariance r') : Prop :=
  ∀ L : ∀ p : Cosphere r', AmplitudeFiber (projection p) →ₗ[ℝ] ℂ,
    let G' (p : Cosphere r') := L p (A'.density p)
    let G (p : Cosphere r) :=
      (cotangentNorm r' p.val ^ 2) • pullbackAmplitudeFiberTest r r' L p (A.density p)
    (Integrable G' A'.control ↔ Integrable G A.control) ∧
      (∫ p, G' p ∂A'.control) = ∫ p, G p ∂A.control

/-- The new trace cancels from the test integral. The radial norm square
remains as the weight of the actual covariance. -/
theorem hasIntrinsicAmplitudeWeightedPushforward_of_traceChange (r r' : Metric (M := M))
    (A : IntrinsicAmplitudeCovariance r) (A' : IntrinsicAmplitudeCovariance r')
    (hTraceMeas : AEMeasurable (intrinsicAmplitudeTraceInMetric r r' A.density) A.control)
    (hTracePos : ∀ᵐ p ∂A.control, 0 < intrinsicAmplitudeTraceInMetric r r' A.density p)
    (hControl : A'.control = (A.control.withDensity (fun p =>
      cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (intrinsicAmplitudeTraceInMetric r r' A.density p))).map
        (renormalizeUnitCosphere r r'))
    (hDensity : ∀ᵐ p ∂A.control, pullbackAmplitudeDensity r r' A'.density p =
      (intrinsicAmplitudeTraceInMetric r r' A.density p)⁻¹ • A.density p) :
    HasIntrinsicAmplitudeWeightedPushforward r r' A A' := by
  intro L G' G
  let F := renormalizeUnitCosphere r r'
  let t := intrinsicAmplitudeTraceInMetric r r' A.density
  let w (p : Cosphere r) := cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (t p)
  let s (p : Cosphere r) := cotangentNorm r' p.val ^ 2
  have hF : MeasurableEmbedding F := measurableEmbedding_renormalizeUnitCosphere r r'
  have hWeight : Measurable (fun p : Cosphere r => cotangentAuxiliaryWeight r' p.val) :=
    ENNReal.measurable_ofReal.comp ((continuous_auxiliaryDualSquare r').comp continuous_subtype_val).measurable
  have hw : AEMeasurable w A.control :=
    hWeight.aemeasurable.mul (ENNReal.measurable_ofReal.comp_aemeasurable hTraceMeas)
  have hwFin : ∀ᵐ p ∂A.control, w p < ⊤ :=
    Eventually.of_forall fun _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  have hEq : (fun p => (w p).toReal • G' (F p)) =ᵐ[A.control] G := by
    filter_upwards [hTracePos, hDensity] with p hp hD
    have hPair : G' (F p) = (t p)⁻¹ • pullbackAmplitudeFiberTest r r' L p (A.density p) :=
      apply_of_cast_eq_smul (renormalizeUnitCosphere_projection r r' p)
        (L (F p)) (A.density p) (A'.density (F p)) _ hD
    have hW : (w p).toReal = s p * t p := by
      change (cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (t p)).toReal = s p * t p
      rw [cotangentAuxiliaryWeight_eq_ofReal_norm_sq_on_cosphere r r' p,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (sq_nonneg _), ENNReal.toReal_ofReal hp.le]
    change (w p).toReal • G' (F p) = s p • pullbackAmplitudeFiberTest r r' L p (A.density p)
    rw [hW, hPair, smul_smul, mul_assoc, mul_inv_cancel₀ hp.ne', mul_one]
  have hMap : A'.control = (A.control.withDensity w).map F := hControl
  constructor
  · rw [hMap, hF.integrable_map_iff, integrable_withDensity_iff_integrable_smul₀' hw hwFin]
    exact integrable_congr hEq
  · rw [hMap, hF.integral_map, integral_withDensity_eq_integral_toReal_smul₀ hw hwFin]
    exact integral_congr_ae hEq

/-- Each integrable fiber-linear test gives a literal complex-measure
pushforward. The same radial normalization is applied to the weighted old
component measure, with arbitrary Borel sets allowed in the identity. -/
theorem intrinsicAmplitude_testMeasure_changeAuxiliary (r r' : Metric (M := M))
    (A : IntrinsicAmplitudeCovariance r) (A' : IntrinsicAmplitudeCovariance r')
    (hChange : HasIntrinsicAmplitudeWeightedPushforward r r' A A')
    (L : ∀ p : Cosphere r', AmplitudeFiber (projection p) →ₗ[ℝ] ℂ)
    (hI : Integrable (fun p => L p (A'.density p)) A'.control) :
    let F := renormalizeUnitCosphere r r'
    let G (p : Cosphere r) :=
      (cotangentNorm r' p.val ^ 2) • pullbackAmplitudeFiberTest r r' L p (A.density p)
    A'.control.withDensityᵥ (fun p => L p (A'.density p)) =
      (A.control.withDensityᵥ G).map F := by
  classical
  intro F G
  let G' (p : Cosphere r') := L p (A'.density p)
  have hF : MeasurableEmbedding F := measurableEmbedding_renormalizeUnitCosphere r r'
  have hGI : Integrable G A.control := (hChange L).1.mp hI
  ext U hU
  rw [VectorMeasure.map_apply _ hF.measurable hU, withDensityᵥ_apply hI hU, withDensityᵥ_apply hGI (hF.measurable hU)]
  let L₀ : ∀ p : Cosphere r', AmplitudeFiber (projection p) →ₗ[ℝ] ℂ :=
    fun p => if p ∈ U then L p else 0
  have hL₀ : (fun p => L₀ p (A'.density p)) = U.indicator G' := by
    funext p
    by_cases hp : p ∈ U <;> simp [L₀, hp, G']
  have hPull₀ : (fun p => (cotangentNorm r' p.val ^ 2) • pullbackAmplitudeFiberTest r r' L₀ p (A.density p)) =
      (F ⁻¹' U).indicator G := by
    funext p
    by_cases hp : F p ∈ U <;> simp [pullbackAmplitudeFiberTest, L₀, F, hp, G]
  have h := (hChange L₀).2
  rw [hL₀, hPull₀, integral_indicator hU, integral_indicator (hF.measurable hU)] at h
  exact h

end Burnett.Microlocal.Overlap
