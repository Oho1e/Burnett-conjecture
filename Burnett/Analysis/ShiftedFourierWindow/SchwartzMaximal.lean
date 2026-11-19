import Burnett.Analysis.ShiftedFourierWindow.RadialKernel
import Mathlib.Analysis.Distribution.FourierSchwartz

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.ShiftedFourierWindow

open Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric
open scoped ENNReal

private theorem decay_five (φ : SchwartzMap Space ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z, (1+‖z‖)^5 * ‖φ z‖ ≤ A := by
  let m : ℕ × ℕ := (5,0)
  let A := (2:ℝ)^5 * (Finset.Iic m).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) φ
  have hd (z : Space) : (1+‖z‖)^5 * ‖φ z‖ ≤ A := by
    simpa [A,m] using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (5,0)) (k := 5) (n := 0) le_rfl le_rfl φ z
  exact ⟨A,(norm_nonneg (φ 0)).trans (by simpa using hd 0),hd⟩

private theorem shifted_decay (φ : SchwartzMap Space ℂ) (A : ℝ)
    (h : ∀ z, (1+‖z‖)^5 * ‖φ z‖ ≤ A) (q z : Space) :
    (1+‖z‖)^5 * ‖φ (z+q)‖ ≤ A * (1+‖q‖)^5 := by
  have ht : ‖z‖ ≤ ‖z+q‖ + ‖q‖ := by simpa using norm_sub_le (z+q) q
  have ht' : 1+‖z‖ ≤ (1+‖q‖)*(1+‖z+q‖) := by
    nlinarith [mul_nonneg (norm_nonneg q) (norm_nonneg (z+q))]
  calc
    _ ≤ ((1+‖q‖)*(1+‖z+q‖))^5 * ‖φ (z+q)‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht' 5) (norm_nonneg _)
    _ = (1+‖q‖)^5 * ((1+‖z+q‖)^5 * ‖φ (z+q)‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_left (h (z+q)) (by positivity : 0 ≤ (1+‖q‖)^5)

/-- Uniform in the physical scale. Translating the reference kernel by q
costs at most a polynomial of degree five in the modulation parameter. -/
theorem shifted_schwartz_kernel_maximal (φ : SchwartzMap Space ℂ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (g : Space → ℝ≥0∞), Measurable g → ∀ (q x : Space) (s : ℝ), 0 < s →
      (∫⁻ y, ENNReal.ofReal (‖φ (s⁻¹ • (x-y)+q)‖ / s^4) * g y) ≤
        (C * ENNReal.ofReal ((1+‖q‖)^5)) * centeredMax g x := by
  obtain ⟨A,hA,hd⟩ := decay_five φ
  let V := volume (closedBall (0:Space) 2)
  refine ⟨ENNReal.ofReal A * V * 2,
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top) (by norm_num),?_⟩
  intro g hg q x s hs
  let Q := (1+‖q‖)^5
  have hs4 : 0 < s^4 := by positivity
  have decay (y : Space) : (1+dist y x / s)^5 * (‖φ (s⁻¹ • (x-y)+q)‖ / s^4) ≤ A*Q / s^4 := by
    have hn : ‖s⁻¹ • (x-y)‖ = dist y x / s := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),dist_comm y x,dist_eq_norm]
      exact inv_mul_eq_div _ _
    rw [← hn,← mul_div_assoc]
    exact div_le_div_of_nonneg_right (shifted_decay φ A hd q _) hs4.le
  have h := polynomial_kernel_maximal g hg _ (fun y => div_nonneg (norm_nonneg _) hs4.le) x s hs
    (A*Q / s^4) (div_nonneg (mul_nonneg hA (by positivity)) hs4.le) decay
  have hv : volume (closedBall (0:Space) (2*s)) = ENNReal.ofReal (s^4) * V := by
    rw [mul_comm (2:ℝ) s, Measure.addHaar_closedBall_mul_of_pos volume 0 hs,
      show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]
  apply h.trans_eq
  congr 1
  rw [hv, ENNReal.ofReal_div_of_pos hs4, ← mul_assoc, ENNReal.div_mul_cancel
    (ENNReal.ofReal_pos.mpr hs4).ne' ENNReal.ofReal_ne_top, ENNReal.ofReal_mul hA]
  dsimp only [Q]
  ac_rfl

end Burnett.Analysis.ShiftedFourierWindow
