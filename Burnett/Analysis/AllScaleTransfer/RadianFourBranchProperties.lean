import Burnett.Analysis.AllScaleTransfer.RadianLowBranchComplete

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.ProjectiveNullCaps

private theorem lowSlotWeight_smul (ϑ : ℝ → ℝ) (κ : ℝ) (t : ℝ) (ht : 0 < t) (p q r : E) :
    lowSlotWeight ϑ κ (t • p) (t • q) (t • r) = lowSlotWeight ϑ κ p q r := by
  unfold lowSlotWeight
  simp only [norm_smul,Real.norm_of_nonneg ht.le]
  have e : κ^2*((t*‖q‖)^2+(t*‖r‖)^2) = t^2*(κ^2*(‖q‖^2+‖r‖^2)) := by ring
  rw [e, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne')]

theorem radianFourBranchSymbol_homogeneous (ϑ : ℝ → ℝ) (κ : ℝ) (m : Joint → ℂ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) (i : Fin 4)
    (t : ℝ) (ht : 0 < t) (p : Joint) :
    radianFourBranchSymbol ϑ κ m i (t • p) = radianFourBranchSymbol ϑ κ m i p := by
  have e : -(t • p.1+t • p.2) = t • (-(p.1+p.2)) := by
    rw [smul_neg,smul_add]
  unfold radianFourBranchSymbol
  rw [hHom t ht p]
  unfold radianFourBranchWeight comparableSlotWeight
  simp only [e,Prod.smul_fst,Prod.smul_snd,lowSlotWeight_smul ϑ κ t ht]

theorem measurable_radianFourBranchSymbol (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ)
    (κ : ℝ) (m : Joint → ℂ) (hm : Measurable m) (i : Fin 4) :
    Measurable (radianFourBranchSymbol ϑ κ m i) := by
  have low {x y z : Joint → E} (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) :
      Measurable (fun p => lowSlotWeight ϑ κ (x p) (y p) (z p)) := by
    unfold lowSlotWeight
    exact hϑ.comp ((hx.norm.pow_const _).div (measurable_const.mul ((hy.norm.pow_const _).add (hz.norm.pow_const _))))
  have third : Measurable (fun p : Joint => -(p.1+p.2)) := (measurable_fst.add measurable_snd).neg
  have weight : Measurable (radianFourBranchWeight ϑ κ i) := by
    fin_cases i
    · exact low measurable_fst measurable_snd third
    · exact low measurable_snd third measurable_fst
    · exact low third measurable_fst measurable_snd
    · exact (((measurable_const.sub (low measurable_fst measurable_snd third)).sub
        (low measurable_snd third measurable_fst)).sub (low third measurable_fst measurable_snd))
  exact (Complex.continuous_ofReal.measurable.comp weight).mul hm

theorem radianFourBranchSymbol_first_low_ratio (ϑ : ℝ → ℝ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (m : Joint → ℂ) (p : Joint) (hq : p.2 ≠ 0) (hm : radianFourBranchSymbol ϑ κ m 0 p ≠ 0) :
    ‖p.1‖ / ‖p.2‖ ≤ 7*κ/4 := by
  have nonzero : lowSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) ≠ 0 := by
    intro h
    apply hm
    change (lowSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) : ℂ) * m p = 0
    rw [h,Complex.ofReal_zero,zero_mul]
  exact ((div_lt_iff₀ (norm_pos_iff.mpr hq)).2
    (lowSlotWeight_nonzero_ratio_margin hCut hκ hκsmall (add_neg_cancel _) hq nonzero)).le

end Burnett.A05
