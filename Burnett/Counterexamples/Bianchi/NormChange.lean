import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

noncomputable section

set_option autoImplicit false

noncomputable section

namespace Burnett.Bianchi.NormChange

open Set Filter MeasureTheory TopologicalSpace
open scoped Topology ENNReal

variable {X Y : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]

/-- The degree-two change of a measure when its chosen ray representative is divided by a. -/
def squareDensity (a : X → ℝ) (x : X) : ℝ≥0∞ := ENNReal.ofReal (a x ^ 2)

def squareWeighted (μ : Measure X) (a : X → ℝ) : Measure X := μ.withDensity (squareDensity a)

def rescaled (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) : Measure Y :=
  Measure.map F (squareWeighted μ a)

theorem squareDensity_measurable (a : X → ℝ) (ha : Continuous a) : Measurable (squareDensity a) :=
  (ha.pow 2).measurable.ennreal_ofReal

omit [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem squareDensity_ne_zero (a : X → ℝ) (hpos : ∀ x, 0 < a x) (x : X) :
    squareDensity a x ≠ 0 := by
  exact (ENNReal.ofReal_pos.mpr (sq_pos_of_pos (hpos x))).ne'

theorem squareWeighted_locallyFinite (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (a : X → ℝ) (ha : Continuous a) : IsLocallyFiniteMeasure (squareWeighted μ a) :=
  IsLocallyFiniteMeasure.withDensity_ofReal (ha.pow 2)

theorem map_homeomorph_locallyFinite (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (F : X ≃ₜ Y) : IsLocallyFiniteMeasure (Measure.map F μ) := by
  constructor
  intro y
  obtain ⟨U, hy, hU, hμU⟩ := μ.exists_isOpen_measure_lt_top (F.symm y)
  have hopen : IsOpen (F '' U) := F.isOpenMap U hU
  refine ⟨F '' U, hopen.mem_nhds ?_, ?_⟩
  · exact ⟨F.symm y, hy, F.apply_symm_apply y⟩
  · rw [Measure.map_apply F.continuous.measurable hopen.measurableSet, F.preimage_image]
    exact hμU

theorem rescaled_locallyFinite (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a) : IsLocallyFiniteMeasure (rescaled μ F a) := by
  letI := squareWeighted_locallyFinite μ a ha
  exact map_homeomorph_locallyFinite (squareWeighted μ a) F

/-- On the actual sigma-compact metrizable section carriers this is a Radon measure. -/
theorem rescaled_regular [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a) : (rescaled μ F a).Regular := by
  letI := rescaled_locallyFinite μ F a ha
  infer_instance

theorem rescaled_innerRegular [PseudoMetrizableSpace Y] [SigmaCompactSpace Y]
    (μ : Measure X) [IsLocallyFiniteMeasure μ]
    (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a) : (rescaled μ F a).InnerRegular := by
  letI := rescaled_locallyFinite μ F a ha
  infer_instance

theorem squareWeighted_null_iff (μ : Measure X) (a : X → ℝ) (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) (S : Set X) : squareWeighted μ a S = 0 ↔ μ S = 0 := by
  constructor
  · intro h
    exact withDensity_absolutelyContinuous' (μ := μ) (squareDensity_measurable a ha).aemeasurable
      (Eventually.of_forall (squareDensity_ne_zero a hpos)) h
  · intro h
    exact withDensity_absolutelyContinuous μ (squareDensity a) h

theorem rescaled_null_iff (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) (S : Set Y) : rescaled μ F a S = 0 ↔ μ (F ⁻¹' S) = 0 := by
  unfold rescaled
  rw [← F.toMeasurableEquiv_coe, MeasurableEquiv.map_apply]
  exact squareWeighted_null_iff μ a ha hpos _

theorem rescaled_supported_iff (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) (S : Set Y) :
    rescaled μ F a Sᶜ = 0 ↔ μ (F ⁻¹' S)ᶜ = 0 := by
  simpa only [preimage_compl] using rescaled_null_iff μ F a ha hpos Sᶜ

theorem integral_rescaled (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (f : Y → ℝ) : ∫ y, f y ∂rescaled μ F a = ∫ x, a x ^ 2 * f (F x) ∂μ := by
  unfold rescaled squareWeighted
  rw [← F.toMeasurableEquiv_coe, integral_map_equiv]
  rw [integral_withDensity_eq_integral_toReal_smul (squareDensity_measurable a ha)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [squareDensity, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul]

theorem integrable_rescaled_iff (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (f : Y → ℝ) : Integrable f (rescaled μ F a) ↔ Integrable (fun x => a x ^ 2 * f (F x)) μ := by
  unfold rescaled squareWeighted
  rw [← F.toMeasurableEquiv_coe, integrable_map_equiv]
  rw [integrable_withDensity_iff_integrable_smul' (squareDensity_measurable a ha)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top)]
  simp only [squareDensity, ENNReal.toReal_ofReal (sq_nonneg _), smul_eq_mul, Function.comp_def]

/-- A genuine degree-two test is preserved, including its Bochner integrability. -/
theorem quadratic_test_preserved (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (f : Y → ℝ) (q : X → ℝ) (hq : ∀ x, a x ^ 2 * f (F x) = q x) :
    (Integrable f (rescaled μ F a) ↔ Integrable q μ) ∧
      (∫ y, f y ∂rescaled μ F a) = ∫ x, q x ∂μ := by
  have heq : (fun x => a x ^ 2 * f (F x)) = q := funext hq
  exact ⟨by rw [integrable_rescaled_iff μ F a ha f, heq],
    by rw [integral_rescaled μ F a ha f, heq]⟩

theorem lintegral_rescaled (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (f : Y → ℝ≥0∞) :
    ∫⁻ y, f y ∂rescaled μ F a = ∫⁻ x, squareDensity a x * f (F x) ∂μ := by
  unfold rescaled squareWeighted
  rw [← F.toMeasurableEquiv_coe, lintegral_map_equiv]
  exact lintegral_withDensity_eq_lintegral_mul_non_measurable μ (squareDensity_measurable a ha)
    (Eventually.of_forall fun x => ENNReal.ofReal_lt_top) _

theorem divided_quadratic_test_preserved (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ)
    (ha : Continuous a) (hpos : ∀ x, 0 < a x) (f : Y → ℝ) (q : X → ℝ)
    (hq : ∀ x, f (F x) = q x / a x ^ 2) :
    (Integrable f (rescaled μ F a) ↔ Integrable q μ) ∧
      (∫ y, f y ∂rescaled μ F a) = ∫ x, q x ∂μ := by
  apply quadratic_test_preserved μ F a ha f q
  intro x
  rw [hq]
  field_simp [(hpos x).ne']

/-- Inverse normalization uses the reciprocal of the same scale on the same ray. -/
def inverseScale (F : X ≃ₜ Y) (a : X → ℝ) (y : Y) : ℝ := (a (F.symm y))⁻¹

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem inverseScale_continuous (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) : Continuous (inverseScale F a) :=
  (ha.comp F.symm.continuous).inv₀ fun y => (hpos (F.symm y)).ne'

omit [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y] in
theorem inverseScale_pos (F : X ≃ₜ Y) (a : X → ℝ) (hpos : ∀ x, 0 < a x) (y : Y) :
    0 < inverseScale F a y := inv_pos.mpr (hpos _)

theorem rescaled_inverse (μ : Measure X) (F : X ≃ₜ Y) (a : X → ℝ) (ha : Continuous a)
    (hpos : ∀ x, 0 < a x) : rescaled (rescaled μ F a) F.symm (inverseScale F a) = μ := by
  apply Measure.ext_of_lintegral
  intro f _
  rw [lintegral_rescaled _ F.symm _ (inverseScale_continuous F a ha hpos)]
  rw [lintegral_rescaled _ F a ha]
  apply lintegral_congr
  intro x
  simp only [squareDensity, inverseScale, F.symm_apply_apply, inv_pow]
  rw [ENNReal.ofReal_inv_of_pos (sq_pos_of_pos (hpos x)), ← mul_assoc]
  change squareDensity a x * (squareDensity a x)⁻¹ * f x = f x
  rw [ENNReal.mul_inv_cancel (squareDensity_ne_zero a hpos x) ENNReal.ofReal_ne_top, one_mul]

end Burnett.Bianchi.NormChange
