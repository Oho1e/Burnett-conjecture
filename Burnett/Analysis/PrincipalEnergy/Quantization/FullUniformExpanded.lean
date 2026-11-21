import Burnett.Analysis.PrincipalEnergy.Quantization.FullActionProperties

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Set Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform Topology

private theorem scaled_input_fourier (χ : E → ℂ) {s : ℝ} (hs : 0 < s) (ξ : E) :
    (𝓕 (expandingInput χ s)) ξ = s^4 • (𝓕 χ) (s • ξ) := by
  calc
    _ = (𝓕⁻ (expandingInput χ s)) (-ξ) := by
      rw [Real.fourierIntegralInv_eq_fourierIntegral_neg,neg_neg]
    _ = s^4 • (𝓕⁻ χ) (s • (-ξ)) := inverseFourier_dilation s hs χ (-ξ)
    _ = _ := by rw [smul_neg,Real.fourierIntegralInv_eq_fourierIntegral_neg,neg_neg]

private theorem action_on_scaled_input (a : E → E → ℂ) (χ : E → ℂ) {s : ℝ} (hs : 0<s) (x : E) :
    firstOrderAction a (expandingInput χ s) x =
      (𝓕⁻ (fun η => a x (s⁻¹ • η) * (𝓕 χ) η)) (s⁻¹ • x) := by
  let q (η : E) := a x (s⁻¹ • η) * (𝓕 χ) η
  have h : (fun ξ => a x ξ * (𝓕 (expandingInput χ s)) ξ) =
      s^4 • (fun ξ => q ((s⁻¹)⁻¹ • ξ)) := by
    funext ξ
    simp only [scaled_input_fourier χ hs,Pi.smul_apply,inv_inv,q,smul_smul,
      inv_mul_cancel₀ hs.ne',one_smul,mul_smul_comm]
  have hMul (F : E → ℂ) : (𝓕⁻ (s^4 • F)) x = s^4 • (𝓕⁻ F) x := by
    simp only [Real.fourierIntegralInv_eq,Pi.smul_apply,smul_comm _ (s^4),integral_smul]
  unfold firstOrderAction
  rw [h,hMul,inverseFourier_dilation _ (inv_pos.mpr hs),smul_smul,inv_pow,
    mul_inv_cancel₀ (pow_ne_zero 4 hs.ne'),one_smul]

/-- A uniform bound for the same actual expanding tests, for every dilation at least one. -/
theorem exists_firstOrderAction_expandingInput_uniform_bound {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (χ : SchwartzMap E ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (s : ℝ), 1 ≤ s → ∀ x, ‖firstOrderAction a (expandingInput χ s) x‖ ≤ M := by
  obtain ⟨C,hC,hOrder⟩ := ha.order 0
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let J (ξ : E) := C*((1+‖ξ‖)*‖F ξ‖)
  have hJ : Integrable J := by
    simpa only [J,add_mul,one_mul,pow_one] using
      (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)).const_mul C
  refine ⟨∫ ξ, J ξ, integral_nonneg (fun ξ => by dsimp [J]; positivity),?_⟩
  intro s hs x
  have hp : 0 < s := zero_lt_one.trans_le hs
  rw [action_on_scaled_input a (χ : E → ℂ) hp,Real.fourierIntegralInv_eq]
  apply norm_integral_le_of_norm_le hJ
  filter_upwards with ξ
  rw [Circle.norm_smul, norm_mul]
  have h1 : ‖s⁻¹ • ξ‖ ≤ ‖ξ‖ := by
    rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hp.le)]
    exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ hp).mpr hs)
  have h2 : ‖a x (s⁻¹ • ξ)‖ ≤ C*(1+‖s⁻¹ • ξ‖) := by
    simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hOrder x (s⁻¹ • ξ)
  exact (mul_le_mul_of_nonneg_right (h2.trans (mul_le_mul_of_nonneg_left
    (add_le_add_left h1 1) hC)) (norm_nonneg _)).trans_eq (by dsimp [J,F]; ring)

end Burnett.Analysis.FirstOrderDyadic
