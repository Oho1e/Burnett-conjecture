import Burnett.Analysis.PrincipalEnergy.Freezing.WeylFrequencyShift
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfrared

set_option autoImplicit false
set_option maxHeartbeats 2350000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit
open scoped FourierTransform RealInnerProductSpace

private theorem phase_at_slanted_base (σ : ℝ) (η x y : E) :
    patchFourierPhase η x * patchFourierPhase (-(σ • η)) x * patchFourierPhase (σ • η) y =
      patchFourierPhase η ((1 - σ) • x + σ • y) := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, inner_neg_left, real_inner_smul_left, inner_add_right, real_inner_smul_right]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem fixed_radian_profile_norm_bound (a : SchwartzMap E ℂ)
    (ar : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (ξ : E) :
    ‖fixedRadianProfile a ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 a := by
  unfold fixedRadianProfile
  rw [← Complex.norm_real, ar]
  exact SchwartzMap.norm_le_seminorm ℝ a _

theorem fixed_radian_profile_measurable (a : SchwartzMap E ℂ) :
    Measurable (fixedRadianProfile a) :=
  (Complex.reCLM.continuous.comp (a.continuous.comp (continuous_const.smul continuous_id))).measurable

/-- The same slanted Fourier integral has the ordinary physical
quantization kernel for any Schwartz frequency profile. -/
theorem separated_radian_quantization_fixed_profile_kernel (σ : ℝ) (a : SchwartzMap E ℂ)
    (ar : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (f u : SchwartzMap E ℂ) (x : E) :
    separatedRadianQuantization σ (fixedRadianProfile a) f u x =
      ∫ y, ((SchwartzMap.fourierTransformCLE ℂ).symm a) (x - y) *
        f ((1 - σ) • x + σ • y) * u y := by
  let b := fixedRadianProfile a
  let B := SchwartzMap.seminorm ℝ 0 0 a
  let K := (SchwartzMap.fourierTransformCLE ℂ).symm a
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have B0 : 0 ≤ B := (norm_nonneg _).trans (fixed_radian_profile_norm_bound a ar 0)
  have bGrow (ξ : E) : ‖b ξ‖ ≤ B * (1 + ‖ξ‖) :=
    (fixed_radian_profile_norm_bound a ar ξ).trans
      (le_mul_of_one_le_right B0 (le_add_of_nonneg_right (norm_nonneg _)))
  let h : E → E := fun y => (1 - σ) • x + σ • y
  let H (z : E × E) := (patchFourierPhase z.1 (h z.2) * F z.1) * (K (x - z.2) * u z.2)
  let args : E × E → E × E := fun z => (z.1, h z.2)
  have hC : Continuous h := continuous_const.add (continuous_const.smul continuous_id)
  have argsC : Continuous args := continuous_fst.prodMk (hC.comp continuous_snd)
  have phaseC : Continuous (fun z : E × E => patchFourierPhase z.1 (h z.2)) := by
    change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ args)
    exact patch_fourier_phase_continuous.comp argsC
  have hH : Continuous H := (phaseC.mul (F.continuous.comp continuous_fst)).mul
    ((K.continuous.comp (continuous_const.sub continuous_snd)).mul (u.continuous.comp continuous_snd))
  let A := SchwartzMap.seminorm ℝ 0 0 K
  have hI : Integrable H ((volume : Measure E).prod volume) := by
    apply ((F.integrable.norm.const_mul A).mul_prod u.integrable.norm).mono' hH.aestronglyMeasurable
    filter_upwards with z
    simp only [H, norm_mul, patch_fourier_phase_norm, one_mul]
    calc
      _ ≤ ‖F z.1‖ * (A * ‖u z.2‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ K _) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  rw [separatedRadianQuantization, radian_fourier_average_eq_integral _
    (slanted_radian_symbol_measurable σ b (fixed_radian_profile_measurable a))
    (slanted_radian_symbol_growth σ b B B0 bGrow)]
  calc
    _ = ∫ η, ∫ y, H (η, y) := by
      apply integral_congr_ae
      filter_upwards with η
      change patchFourierPhase η x * F η *
        radianAction (fun ξ => b (ξ + tau • (σ • η))) u x = _
      rw [radian_action_shift b, fixedRadianProfile_convolution a ar, ← integral_const_mul, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      rw [patch_modulated_schwartz_apply]
      dsimp only [H, h]
      rw [← phase_at_slanted_base]
      ring
    _ = ∫ y, ∫ η, H (η, y) :=
      integral_integral_swap (f := fun η y => H (η, y)) hI
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      let p := (1 - σ) • x + σ • y
      have hEq : (fun η : E => H (η,y)) = fun η => (patchFourierPhase η p * F η) * (K (x-y) * u y) := rfl
      rw [hEq, integral_mul_const]
      have inv := congrFun (f.continuous.fourier_inversion f.integrable F.integrable) p
      rw [Real.fourierIntegralInv_eq'] at inv
      have fi : (∫ η, patchFourierPhase η p * F η) = f p := by
        simpa only [Burnett.Microlocal.Overlap.baseFourierPhase, tau, smul_eq_mul] using inv
      rw [fi]
      change f p * (K (x-y) * u y) = K (x-y) * f p * u y
      ring

/-- The half shift in physical coordinates evaluates the spatial factor
at the real midpoint in the genuine Weyl kernel. -/
theorem separated_radian_weyl_fixed_profile_kernel (a : SchwartzMap E ℂ)
    (ar : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (f u : SchwartzMap E ℂ) (x : E) :
    separatedRadianQuantization (1 / 2) (fixedRadianProfile a) f u x =
      ∫ y, ((SchwartzMap.fourierTransformCLE ℂ).symm a) (x - y) * f ((1 / 2 : ℝ) • (x + y)) * u y := by
  rw [separated_radian_quantization_fixed_profile_kernel (1 / 2) a ar]
  norm_num [smul_add]

end Burnett.A03
