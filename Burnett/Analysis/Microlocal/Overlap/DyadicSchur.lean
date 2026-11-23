import Burnett.Analysis.PrincipalEnergy.Quantization.ConvolutionEnvelope
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel (E dyadicScale)
open Burnett.Analysis.FirstOrderDyadic (convolution_envelope_action_norm_le)
open scoped ENNReal

/-- The inverse fifth-power profile is integrable in four dimensions. -/
def fifthProfile (z : E) : ℝ := ((1 + ‖z‖) ^ 5)⁻¹

theorem fifthProfile_nonneg (z : E) : 0 ≤ fifthProfile z := by
  unfold fifthProfile
  positivity

theorem fifthProfile_measurable : Measurable fifthProfile := by
  unfold fifthProfile
  fun_prop

theorem fifthProfile_integrable : Integrable fifthProfile := by
  have hdim : (Module.finrank ℝ E : ℝ) < 5 := by norm_num [finrank_euclideanSpace_fin]
  apply (integrable_one_add_norm (μ := (volume : Measure E)) hdim).congr
  filter_upwards with z
  rw [Real.rpow_neg (by positivity)]
  norm_num [fifthProfile, Real.rpow_natCast]

/-- An inverse fifth-power kernel envelope after one derivative of scale gain. -/
def overlapSchurEnvelope (C q s : ℝ) (z : E) : ℝ :=
  C * s ^ 3 * fifthProfile ((s * q) • z)

theorem overlapSchurEnvelope_integral (C q s : ℝ) (hq : 0 < q) (hs : 0 < s) :
    (∫ z, overlapSchurEnvelope C q s z) = (C / q ^ 4 * ∫ z, fifthProfile z) / s := by
  have h := Measure.integral_comp_smul_of_nonneg (volume : Measure E) fifthProfile (s * q)
    (hR := mul_nonneg hs.le hq.le)
  rw [show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin] at h
  unfold overlapSchurEnvelope
  rw [integral_const_mul, h, smul_eq_mul]
  field_simp [hs.ne', hq.ne']

/-- Both integration directions give the same inverse-scale Schur gain. -/
theorem overlapKernel_action_norm_le (K : E → E → ℂ) (hK : Measurable (uncurry K))
    (C q s : ℝ) (hC : 0 ≤ C) (hq : 0 < q) (hs : 0 < s)
    (hbound : ∀ x y, ‖K x y‖ ≤ C * s ^ 3 / (1 + s * q * ‖x - y‖) ^ 5)
    (f : E → ℂ) (hf : Measurable f) (hf₁ : Integrable f) (hf₂ : MemLp f 2 volume) :
    ∃ hA : MemLp (fun x => ∫ y, K x y * f y) 2 volume,
      ‖hA.toLp (fun x => ∫ y, K x y * f y)‖ ≤
        ((C / q ^ 4 * ∫ z, fifthProfile z) / s) * ‖hf₂.toLp f‖ := by
  let D := overlapSchurEnvelope C q s
  have hD : Measurable D :=
    measurable_const.mul (fifthProfile_measurable.comp (measurable_const.smul measurable_id))
  have hD₀ (z : E) : 0 ≤ D z :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hs.le _)) (fifthProfile_nonneg _)
  have hI : Integrable D := (fifthProfile_integrable.comp_smul (mul_ne_zero hs.ne' hq.ne')).const_mul _
  have hDom (x y : E) : ‖K x y‖ ≤ D (x - y) := by
    simpa only [D, overlapSchurEnvelope, fifthProfile, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hs.le hq.le), div_eq_mul_inv] using hbound x y
  obtain ⟨hA, hnorm⟩ := convolution_envelope_action_norm_le K hK D hD hD₀ hI hDom f hf hf₁ hf₂
  exact ⟨hA, by simpa only [D, overlapSchurEnvelope_integral C q s hq hs] using hnorm⟩

/-- Every dyadic shell contributes a summable inverse-scale factor. -/
theorem summable_overlapShell_bound (C q : ℝ) :
    Summable (fun j : ℕ => (C / q ^ 4 * ∫ z, fifthProfile z) / dyadicScale j) := by
  have h : Summable (fun j : ℕ => ((2 : ℝ)⁻¹) ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  simpa only [dyadicScale, div_eq_mul_inv, inv_pow] using h.mul_left (C / q ^ 4 * ∫ z, fifthProfile z)

end Burnett.Microlocal.Overlap
