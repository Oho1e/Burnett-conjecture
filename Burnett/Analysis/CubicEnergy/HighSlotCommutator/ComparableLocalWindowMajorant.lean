import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric
open scoped ENNReal

/-- Low-frequency Fourier windows, including fixed normalized spatial
translations, are bounded by the maximal function at every center in the
receiving ball. The shift cost also accounts for changing the center. -/
theorem exists_windowTest_ball_maximal_bound (a : SchwartzMap E ℂ) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (f : SchwartzMap E ℂ) {u s : ℝ}, 0<u → 0<s →
      ∀ (Y x y : E), y ∈ ball x s →
      ‖windowTest a f (u*s) (x-s • Y)‖ₑ ≤
        C*ENNReal.ofReal ((1+u⁻¹*(‖Y‖+1))^5) * centeredMax (fun z => ‖f z‖ₑ) y := by
  let ψ := (SchwartzMap.fourierTransformCLE ℂ).symm a
  obtain ⟨C,hC,bound⟩ := shifted_schwartz_kernel_maximal ψ
  refine ⟨C,hC,?_⟩
  intro f u s hu hs Y x y hy
  let S := u*s
  have hS : 0<S := mul_pos hu hs
  let q := S⁻¹ • (x-y) - u⁻¹ • Y
  have sc : S⁻¹*s = u⁻¹ := by dsimp only [S]; field_simp
  have hnorm : ‖q‖ ≤ u⁻¹*(‖Y‖+1) := by
    have hxy : ‖x-y‖ ≤ s := by simpa only [mem_ball,dist_comm y x,dist_eq_norm] using (mem_ball.mp hy).le
    unfold q
    calc
      _ ≤ ‖S⁻¹ • (x-y)‖ + ‖u⁻¹ • Y‖ := norm_sub_le _ _
      _ = S⁻¹*‖x-y‖+u⁻¹*‖Y‖ := by
        rw [norm_smul,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le),
          Real.norm_of_nonneg (inv_nonneg.mpr hu.le)]
      _ ≤ S⁻¹*s+u⁻¹*‖Y‖ := by gcongr
      _ = _ := by rw [sc]; ring
  have relative (z : E) : S⁻¹ • (x-s • Y-z)+0 = S⁻¹ • (y-z)+q := by
    unfold q
    simp only [add_zero,smul_sub,smul_smul,sc]
    abel
  have action := windowTest_translate a f S 0 hS (x-s • Y) (0 : E)
  simp only [smul_zero,sub_zero,neg_zero,zero_div] at action
  change ‖windowTest a f S (x-s • Y)‖ₑ ≤ _
  rw [action,shifted_window_physical a f S hS]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  have eq (z : E) :
      ‖((S^4)⁻¹ • ψ (S⁻¹ • (x-s • Y-z)+0)) * f z‖ₑ =
        ENNReal.ofReal (‖ψ (S⁻¹ • (y-z)+q)‖/S^4)*‖f z‖ₑ := by
    rw [relative,enorm_mul,← ofReal_norm_eq_enorm,norm_smul,Real.norm_of_nonneg
      (inv_nonneg.mpr (pow_nonneg hS.le _)),inv_mul_eq_div]
  change (∫⁻ z, ‖((S^4)⁻¹ • ψ (S⁻¹ • (x-s • Y-z)+0))*f z‖ₑ) ≤ _
  simp_rw [eq]
  refine (bound (fun z => ‖f z‖ₑ) f.continuous.measurable.enorm q y S hS).trans ?_
  exact mul_le_mul_right' (mul_le_mul_left' (ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (by positivity) (add_le_add_left hnorm 1) _)) _) _

end Burnett.A06
