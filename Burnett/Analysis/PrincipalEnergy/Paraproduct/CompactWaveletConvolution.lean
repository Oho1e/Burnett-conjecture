import Burnett.Analysis.PrincipalEnergy.Commutator.WaveletOperator

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function

private theorem waveletKernel_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) :
    Integrable (compactWaveletKernel ψ s) (volume : Measure Space) :=
  (ψ.integrable.comp_smul (inv_ne_zero hs.ne')).smul _

private theorem wavelet_convolution_integrable_product (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    {f : Space → ℂ} (hf : Integrable f volume) :
    Integrable (uncurry (fun x y => compactWaveletKernel ψ s (x-y)*f y))
      ((volume : Measure Space).prod volume) :=
  (measurePreserving_sub_prod (volume : Measure Space) volume).integrable_comp_of_integrable
    ((waveletKernel_integrable ψ s hs).mul_prod hf)

theorem compactWaveletAction_integrable (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    {f : Space → ℂ} (hf : Integrable f volume) : Integrable (compactWaveletAction ψ s f) volume :=
  (wavelet_convolution_integrable_product ψ s hs hf).integral_prod_left

/-- Normalization of the actual constant-input spatial convolution. -/
theorem compactWaveletAction_one (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s) (x : Space) :
    compactWaveletAction ψ s (fun _ => 1) x = ∫ z, ψ z := by
  let K := compactWaveletKernel ψ s
  have hK := waveletKernel_integrable ψ s hs
  have hT := (volume : Measure Space).measurePreserving_sub_left x
  unfold compactWaveletAction
  simp only [mul_one]
  change (∫ y, K (x-y)) = _
  rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hK.aestronglyMeasurable),
    hT.map_eq]
  exact compactWaveletKernel_integral_eq ψ s hs

/-- The actual spatial convolution has integral equal to the product of
the window and input masses. -/
theorem compactWaveletAction_integral (ψ : SchwartzMap Space ℂ) (s : ℝ) (hs : 0<s)
    {f : Space → ℂ} (hf : Integrable f volume) :
    (∫ x, compactWaveletAction ψ s f x) = (∫ x, ψ x)*(∫ x, f x) := by
  let K := compactWaveletKernel ψ s
  have hK : Integrable K (volume : Measure Space) := waveletKernel_integrable ψ s hs
  unfold compactWaveletAction
  rw [integral_integral_swap (wavelet_convolution_integrable_product ψ s hs hf)]
  change (∫ y, ∫ x, K (x-y)*f y) = _
  have hMass (y : Space) : (∫ x, K (x-y)*f y) = (∫ z, ψ z)*f y := by
    rw [integral_mul_const]
    have hT : MeasurePreserving (fun x : Space => x-y) volume volume := by
      simpa only [sub_eq_add_neg] using measurePreserving_add_right (volume : Measure Space) (-y)
    rw [← integral_map hT.measurable.aemeasurable (by rw [hT.map_eq]; exact hK.aestronglyMeasurable),
      hT.map_eq]
    rw [show (∫ z, K z) = ∫ z, ψ z from compactWaveletKernel_integral_eq ψ s hs]
  simp_rw [hMass]
  rw [integral_const_mul]

theorem compactWaveletAction_norm_le_integral_norm (ψ : SchwartzMap Space ℂ) (s : ℝ)
    {f : Space → ℂ} (hf : Integrable f volume) (x : Space) :
    ‖compactWaveletAction ψ s f x‖ ≤
      (|(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 ψ)*(∫ y, ‖f y‖) := by
  let A := |(s^4)⁻¹| * SchwartzMap.seminorm ℝ 0 0 ψ
  have hDom (y : Space) : ‖compactWaveletKernel ψ s (x-y)*f y‖ ≤ A*‖f y‖ := by
    rw [norm_mul,compactWaveletKernel,norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (SchwartzMap.norm_le_seminorm ℝ ψ _) (abs_nonneg _)) (norm_nonneg _)
  calc
    _ ≤ ∫ y, ‖compactWaveletKernel ψ s (x-y)*f y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, A*‖f y‖ := integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) (hf.norm.const_mul A) (Eventually.of_forall hDom)
    _ = _ := by rw [integral_const_mul]

end Burnett.Analysis.CarlesonEmbedding
