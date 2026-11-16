import Burnett.Analysis.Fourier.Modulation

noncomputable section

namespace Burnett.Fourier

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem modulate_integrable (k : V) {f : V → ℂ} (hf : Integrable f (volume : Measure V)) :
    Integrable (modulate k f) (volume : Measure V) := by
  have hc : Continuous (fun x : V => Real.fourierChar ⟪x, k⟫) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  apply hf.norm.mono' (hc.aestronglyMeasurable.smul hf.aestronglyMeasurable)
  filter_upwards with x
  exact (Circle.norm_smul _ _).le

theorem fourier_add {f g : V → ℂ} (hf : Integrable f (volume : Measure V))
    (hg : Integrable g volume) : 𝓕 (f + g) = 𝓕 f + 𝓕 g :=
  VectorFourier.fourierIntegral_add Real.continuous_fourierChar continuous_inner hf hg

theorem fourier_const_smul (c : ℂ) (f : V → ℂ) : 𝓕 (c • f) = c • 𝓕 f :=
  VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (innerₗ V) f c

omit [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] in
theorem cosine_eq_two_modulations (k : V) (f : V → ℂ) :
    (fun x => f x * (Real.cos ⟪k, x⟫ : ℂ)) =
      (1/2 : ℂ) • (modulate ((2 * Real.pi)⁻¹ • k) f +
        modulate (-((2 * Real.pi)⁻¹ • k)) f) := by
  funext x
  simp only [Pi.smul_apply, Pi.add_apply, modulate, Circle.smul_def, smul_eq_mul,
    Real.fourierChar_apply, inner_smul_right, inner_neg_right]
  have hangle : 2 * Real.pi * ((2 * Real.pi)⁻¹ * ⟪x, k⟫) = ⟪k, x⟫ := by
    rw [← mul_assoc, mul_inv_cancel₀ (mul_ne_zero (by norm_num) Real.pi_ne_zero),
      one_mul, real_inner_comm]
  rw [hangle]
  have hangle' : 2 * Real.pi * -((2 * Real.pi)⁻¹ * ⟪x, k⟫) = -⟪k, x⟫ := by
    rw [mul_neg, hangle]
  rw [hangle', Complex.ofReal_cos, Complex.cos]
  push_cast
  ring

theorem fourier_cosine (k : V) {f : V → ℂ} (hf : Integrable f (volume : Measure V)) (ξ : V) :
    𝓕 (fun x => f x * (Real.cos ⟪k, x⟫ : ℂ)) ξ =
      (1/2 : ℂ) * (𝓕 f (ξ - (2 * Real.pi)⁻¹ • k) +
        𝓕 f (ξ + (2 * Real.pi)⁻¹ • k)) := by
  rw [cosine_eq_two_modulations, fourier_const_smul,
    fourier_add (modulate_integrable _ hf) (modulate_integrable _ hf)]
  simp only [Pi.smul_apply, Pi.add_apply, fourier_modulate, smul_eq_mul, sub_neg_eq_add]

theorem cosine_integrable (k : V) {f : V → ℂ} (hf : Integrable f (volume : Measure V)) :
    Integrable (fun x => f x * (Real.cos ⟪k, x⟫ : ℂ)) (volume : Measure V) := by
  rw [cosine_eq_two_modulations]
  exact ((modulate_integrable _ hf).add (modulate_integrable _ hf)).smul _

end Burnett.Fourier
