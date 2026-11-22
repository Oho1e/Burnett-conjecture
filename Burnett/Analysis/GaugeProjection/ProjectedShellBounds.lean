import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.P01

open MeasureTheory Set Filter Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform Topology NNReal

private theorem scale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

private theorem integral_scale {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (g : E → F) (j : ℕ) :
    (∫ z, g (dyadicScale j • z)) = (dyadicScale j ^ 4)⁻¹ • ∫ z, g z := by
  simpa only [finrank_euclideanSpace_fin] using
    Measure.integral_comp_smul_of_nonneg (volume : Measure E) g
      (dyadicScale j) (hR := (scale_pos j).le)

private theorem inverseAnnularSchwartz_integral_zero (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) :
    (∫ z, inverseAnnularSchwartz m hm z) = 0 := by
  have hf : 𝓕 (inverseAnnularSchwartz m hm : E → ℂ) 0 = annularSchwartz m hm 0 := by
    change SchwartzMap.fourierTransformCLE ℂ
      ((SchwartzMap.fourierTransformCLE ℂ).symm (annularSchwartz m hm)) 0 = _
    rw [ContinuousLinearEquiv.apply_symm_apply]
  have h0 : annularSchwartz m hm 0 = 0 := by
    change annularSymbol m 0 = 0
    simp [annularSymbol, annulus_eq_zero_near]
  simpa [Real.fourierIntegral_eq, h0] using hf

private theorem shell_integral_zero (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    (∫ z, shellKernel m hm j z) = 0 := by
  simp only [shellKernel, integral_smul, integral_scale,
    inverseAnnularSchwartz_integral_zero, smul_zero]

theorem projectedShellKernel_integrable (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    Integrable (shellKernel m hm j) := by
  exact ((inverseAnnularSchwartz m hm).integrable.comp_smul
    (scale_pos j).ne').smul (dyadicScale j ^ 4)

private theorem shell_norm_integral (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    (∫ z, ‖shellKernel m hm j z‖) = ∫ z, ‖inverseAnnularSchwartz m hm z‖ := by
  simp only [shellKernel, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (scale_pos j).le 4), integral_const_mul]
  rw [integral_scale (fun z => ‖inverseAnnularSchwartz m hm z‖) j,
    smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero 4 (scale_pos j).ne'), one_mul]

private theorem shell_norm_moment_eq (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (z : E) :
    ‖shellKernel m hm j z‖ * ‖z‖ =
      (dyadicScale j ^ 4 * (dyadicScale j)⁻¹) *
        (‖inverseAnnularSchwartz m hm (dyadicScale j • z)‖ * ‖dyadicScale j • z‖) := by
  let s := dyadicScale j
  have hs : 0 < s := scale_pos j
  change ‖s ^ 4 • inverseAnnularSchwartz m hm (s • z)‖ * ‖z‖ =
    (s ^ 4 * s⁻¹) * (‖inverseAnnularSchwartz m hm (s • z)‖ * ‖s • z‖)
  simp only [norm_smul, Real.norm_of_nonneg hs.le, Real.norm_of_nonneg (pow_nonneg hs.le _)]
  change _ = s ^ 4 * s⁻¹ * (‖inverseAnnularSchwartz m hm (s • z)‖ * (s * ‖z‖))
  field_simp

private theorem shell_moment_integrable (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    Integrable (fun z => ‖shellKernel m hm j z‖ * ‖z‖) := by
  let k := inverseAnnularSchwartz m hm
  have hi : Integrable (fun z : E => ‖k z‖ * ‖z‖) := by
    simpa only [pow_one, mul_comm] using k.integrable_pow_mul volume 1
  simpa only [shell_norm_moment_eq] using (hi.comp_smul (scale_pos j).ne').const_mul
    (dyadicScale j ^ 4 * (dyadicScale j)⁻¹)

private theorem shell_moment_integral (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    (∫ z, ‖shellKernel m hm j z‖ * ‖z‖) =
      (dyadicScale j)⁻¹ * ∫ z, ‖inverseAnnularSchwartz m hm z‖ * ‖z‖ := by
  simp only [shell_norm_moment_eq, integral_const_mul]
  rw [integral_scale (fun z => ‖inverseAnnularSchwartz m hm z‖ * ‖z‖) j, smul_eq_mul]
  field_simp [(scale_pos j).ne']

theorem integral_convolution_swap (k f : E → ℂ) (x : E) :
    (∫ y, k (x-y) * f y) = ∫ z, k z * f (x-z) := by
  simpa only [sub_sub_cancel] using
    integral_sub_left_eq_self (fun z : E => k z * f (x-z)) (volume : Measure E) x

theorem norm_integral_convolution_le (k f : E → ℂ) (hk : Integrable k)
    (x : E) (M : ℝ) (hf : ∀ y, ‖f y‖ ≤ M) :
    ‖∫ y, k (x-y) * f y‖ ≤ (∫ z, ‖k z‖) * M := by
  rw [integral_convolution_swap, ← integral_mul_const]
  refine norm_integral_le_of_norm_le (hk.norm.mul_const M) ?_
  exact Eventually.of_forall fun z => by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hf (x-z)) (norm_nonneg _)

/-- The same physical dyadic shell is bounded by both its mass and its
first moment after subtracting the constant value of the input at x. -/
theorem projected_shell_convolution_bounds (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ)
    (f : E → ℂ) (x : E) (M : ℝ) (hf : ∀ y, ‖f y‖ ≤ M)
    (L : ℝ≥0) (hL : LipschitzWith L f) :
    ‖∫ y, shellKernel m hm j (x-y) * f y‖ ≤
      (∫ z, ‖inverseAnnularSchwartz m hm z‖) * M ∧
    ‖∫ y, shellKernel m hm j (x-y) * f y‖ ≤
      (∫ z, ‖inverseAnnularSchwartz m hm z‖ * ‖z‖) *
        (dyadicScale j)⁻¹ * (L : ℝ) := by
  let k := shellKernel m hm j
  have hk : Integrable k := projectedShellKernel_integrable m hm j
  refine ⟨?_, ?_⟩
  · rw [← shell_norm_integral m hm j]
    exact norm_integral_convolution_le k f hk x M hf
  have hprod : Integrable (fun z => k z * f (x-z)) := by
    refine (hk.norm.mul_const M).mono'
      (hk.aestronglyMeasurable.mul
        ((hL.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)) ?_
    exact Eventually.of_forall fun z => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hf (x-z)) (norm_nonneg _)
  have hcancel : (∫ z, k z * (f (x-z) - f x)) = ∫ z, k z * f (x-z) := by
    simp only [mul_sub]
    rw [integral_sub hprod (hk.mul_const (f x)), integral_mul_const,
      show (∫ z, k z) = 0 from shell_integral_zero m hm j, zero_mul, sub_zero]
  rw [integral_convolution_swap, ← hcancel, mul_comm (∫ z, _) (dyadicScale j)⁻¹,
    ← shell_moment_integral m hm j, ← integral_mul_const]
  refine norm_integral_le_of_norm_le ((shell_moment_integrable m hm j).mul_const (L : ℝ)) ?_
  refine Eventually.of_forall fun z => ?_
  rw [norm_mul, mul_assoc, mul_comm ‖z‖]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [show x-z-x = -z by abel, norm_neg] using hL.norm_sub_le (x-z) x

end Burnett.P01
