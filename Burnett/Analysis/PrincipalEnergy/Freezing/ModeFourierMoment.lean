import Burnett.Analysis.PrincipalEnergy.Freezing.ProfileFourierMoment
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform RealInnerProductSpace

private theorem one_add_norm_pow_le (r : ℕ) (η : E) :
    (1 + ‖η‖) ^ r ≤ 2 ^ r * (1 + ‖η‖ ^ r) := by
  by_cases small : ‖η‖ ≤ 1
  · have h : 1 + ‖η‖ ≤ 2 := by linarith
    calc
      _ ≤ (2 : ℝ) ^ r := pow_le_pow_left₀ (by positivity) h _
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (le_add_of_nonneg_right (by positivity))
  · have h : 1 + ‖η‖ ≤ 2 * ‖η‖ := by linarith [lt_of_not_ge small]
    calc
      _ ≤ (2 * ‖η‖) ^ r := pow_le_pow_left₀ (by positivity) h _
      _ ≤ _ := by rw [mul_pow]; gcongr; linarith

/-- The absolute Fourier moment of a genuine modulation grows by at most the
corresponding power of the modulation frequency. -/
theorem patch_fourier_moment_modulated (r : ℕ) (f : SchwartzMap E ℂ) (q : E) :
    patchFourierMoment r (patchModulatedSchwartz q f) ≤
      (1 + ‖q‖) ^ r * 2 ^ r *
        (patchFourierMoment 0 f + patchFourierMoment r f) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let U := SchwartzMap.fourierTransformCLM ℂ (patchModulatedSchwartz q f)
  let C := (1 + ‖q‖) ^ r * 2 ^ r
  let H (η : E) := ‖η + q‖ ^ r * ‖F η‖
  have rewrite :
      patchFourierMoment r (patchModulatedSchwartz q f) = ∫ η, H η := by
    unfold patchFourierMoment
    simp_rw [patch_modulated_schwartz_fourier]
    have eq : (fun η : E => ‖η‖ ^ r * ‖𝓕 (f : E → ℂ) (η - q)‖) =
        fun η => H (η + -q) := by
      funext η
      simp only [H, add_assoc, neg_add_cancel, add_zero, sub_eq_add_neg]
      rfl
    rw [eq, integral_add_right_eq_self H (-q)]
  rw [rewrite]
  have hH : Integrable H := by
    have int := (U.integrable_pow_mul volume r).comp_add_right q
    convert int using 1
    funext η
    dsimp only [H]
    change ‖η + q‖ ^ r * ‖F η‖ =
      ‖η + q‖ ^ r * ‖𝓕 (patchModulatedSchwartz q f : E → ℂ) (η + q)‖
    rw [patch_modulated_schwartz_fourier, add_sub_cancel_right]
    rfl
  have hi := (F.integrable.norm.add (F.integrable_pow_mul volume r)).const_mul C
  have major (η : E) : H η ≤ C * (‖F η‖ + ‖η‖ ^ r * ‖F η‖) := by
    have tri : ‖η + q‖ ≤ (1 + ‖q‖) * (1 + ‖η‖) := by
      apply (norm_add_le _ _).trans
      nlinarith [norm_nonneg η, norm_nonneg q, mul_nonneg (norm_nonneg η) (norm_nonneg q)]
    have first := pow_le_pow_left₀ (norm_nonneg (η + q)) tri r
    rw [mul_pow] at first
    calc
      H η ≤ ((1 + ‖q‖) ^ r * (1 + ‖η‖) ^ r) * ‖F η‖ :=
        mul_le_mul_of_nonneg_right first (norm_nonneg _)
      _ ≤ ((1 + ‖q‖) ^ r * (2 ^ r * (1 + ‖η‖ ^ r))) * ‖F η‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_add_norm_pow_le r η)
          (by positivity)) (norm_nonneg _)
      _ = _ := by dsimp only [C]; ring
  refine (integral_mono hH hi major).trans_eq ?_
  simp only [Pi.add_apply]
  rw [integral_const_mul, integral_add F.integrable.norm (F.integrable_pow_mul volume r)]
  simp only [patchFourierMoment, pow_zero, one_mul, C]
  rfl

/-- A coordinate derivative consumes exactly one further frequency moment. -/
theorem patch_fourier_moment_partial (r : ℕ) (j : Index) (f : SchwartzMap E ℂ) :
    patchFourierMoment r (energyPartial j f) ≤ tau * patchFourierMoment (r + 1) f := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let U := SchwartzMap.fourierTransformCLM ℂ (energyPartial j f)
  have hp : 0 ≤ tau := by unfold tau; positivity
  unfold patchFourierMoment
  rw [← integral_const_mul]
  apply integral_mono (U.integrable_pow_mul volume r) ((F.integrable_pow_mul volume (r + 1)).const_mul tau)
  intro η
  change ‖η‖ ^ r * ‖𝓕 (energyPartial j f : E → ℂ) η‖ ≤ tau * (‖η‖ ^ (r + 1) * ‖𝓕 (f : E → ℂ) η‖)
  rw [energyPartial_fourier, norm_mul, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    norm_mul, Real.norm_of_nonneg hp, pow_succ]
  have coord := PiLp.norm_apply_le η j
  calc
    _ ≤ ‖η‖ ^ r * (tau * ‖η‖ * ‖𝓕 (f : E → ℂ) η‖) := by gcongr
    _ = _ := by ring

end Burnett.A03
