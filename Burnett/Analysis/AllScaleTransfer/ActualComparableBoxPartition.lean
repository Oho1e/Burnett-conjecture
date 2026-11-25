import Burnett.Analysis.AllScaleTransfer.FixedShiftRadianBoxTransfer
import Burnett.Analysis.AllScaleTransfer.ComparableIntegerRadialShifts

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.A05

open Set Finset Metric
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

private theorem thirdProfile_hasCompactSupport (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    HasCompactSupport (fun z : E => (comparableThirdCutoff a b 1 z : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2*b))
  intro z hz
  have hne : comparableThirdCutoff a b 1 z ≠ 0 := by
    intro h
    exact hz (by simp only [h, Complex.ofReal_zero])
  have hSupp := (comparableThirdCutoff_smooth_support ha hab (by norm_num : (0 : ℝ) < 1)).2
    (subset_tsupport _ hne)
  exact mem_closedBall.mpr (by simpa only [dist_zero_right, mul_one] using hSupp.2)

/-- The same actual comparable third annulus as a fixed Schwartz profile. -/
def comparableThirdSchwartzProfile (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) : SchwartzMap E ℂ :=
  (thirdProfile_hasCompactSupport a b ha hab).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp
      (comparableThirdCutoff_smooth_support ha hab (by norm_num : (0 : ℝ) < 1)).1)

theorem comparableThirdSchwartzProfile_scaled (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (r : ℝ) (w : E) :
    comparableThirdSchwartzProfile a b ha hab (r⁻¹ • w) = (comparableThirdCutoff a b r w : ℂ) := by
  change (comparableThirdCutoff a b 1 (r⁻¹ • w) : ℂ) = _
  have low (c : ℝ) : radialLowCutoff c (r⁻¹ • w) = radialLowCutoff (c*r) w := by
    unfold radialLowCutoff
    rw [smul_smul, mul_inv_rev, mul_comm c⁻¹ r⁻¹]
  simp only [comparableThirdCutoff, mul_one]
  rw [low, low, show a/2*r = a*r/2 by ring]

private theorem comparableLower_pos (κ L U : ℝ) (hκ : 0 < κ) (hL : 0 < L) (hU : 0 < U) :
    0 < comparableRadialLower κ L U := lt_min (by norm_num) (by positivity)

private theorem comparableLower_le_upper (κ L U : ℝ) :
    comparableRadialLower κ L U ≤ comparableRadialUpper κ L U :=
  (min_le_left _ _).trans ((show (1/2 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _))

def comparableRadialThirdProfile (κ L U : ℝ) (hκ : 0 < κ) (hL : 0 < L) (hU : 0 < U) :
    SchwartzMap E ℂ :=
  comparableThirdSchwartzProfile (comparableRadialLower κ L U) (comparableRadialUpper κ L U)
    (comparableLower_pos κ L U hκ hL hU) (comparableLower_le_upper κ L U)

/-- Inserting the actual comparable third annulus and summing the original
windows over the retained signed shifts reconstructs one on the genuine
comparable support. The reference scale is the second slot. -/
theorem exists_comparable_fixedShift_box_partition {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ L U : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hL : 0 < L) (hU : 0 < U) :
    ∃ N : ℕ, ∀ (A : E ≃L[ℝ] E) (p q : E), q ≠ 0 →
      let w := -(p+q)
      comparableSlotWeight ϑ κ (A p) (A q) (A w) ≠ 0 →
      (L*‖p‖ ≤ ‖A p‖ ∧ ‖A p‖ ≤ U*‖p‖) →
      (L*‖q‖ ≤ ‖A q‖ ∧ ‖A q‖ ≤ U*‖q‖) →
      (L*‖w‖ ≤ ‖A w‖ ∧ ‖A w‖ ≤ U*‖w‖) →
      let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
      let d := comparableRadialThirdProfile κ L U hκ hL hU
      (∑ k ∈ I, ∑' j : ℤ, radianFixedShiftBoxBlock d (fun _ => 1) k j (p,q)) = 1 := by
  obtain ⟨N, hShift⟩ := exists_comparable_integerRadialWindow_finiteShifts hCut hFlat
    κ L U hκ hκsmall hL hU
  refine ⟨N, ?_⟩
  intro A p q hq w hComp hpA hqA hwA I d
  let F (k j : ℤ) := (integerRadialWindow (j+k) p : ℂ) * (integerRadialWindow j q : ℂ) *
    d ((2 : ℝ)^(-j) • w)
  obtain ⟨Q, _, hQ⟩ := exists_integerRadialWindow_support_card_le_three q
  have hF (k : ℤ) : (∑' j : ℤ, F k j) = ∑ j ∈ Q, F k j := by
    apply tsum_eq_sum
    intro j hj
    simp only [F, hQ j hj, Complex.ofReal_zero, mul_zero, zero_mul]
  have same (k j : ℤ) : radianFixedShiftBoxBlock d (fun _ => 1) k j (p,q) = F k j := by
    simp only [radianFixedShiftBoxBlock, F, w, one_mul]
  have perHigh (j : ℤ) : (∑ k ∈ I, F k j) = (integerRadialWindow j q : ℂ) := by
    by_cases hj : integerRadialWindow j q = 0
    · simp only [F, hj, Complex.ofReal_zero, mul_zero, zero_mul, Finset.sum_const_zero]
    have hr : 0 < (2 : ℝ)^j := by positivity
    have hAnn := radialAnnularCutoff_nonzero hr hj
    have band := comparable_normalized_triad_annulus hCut hFlat A hκ hκsmall hL hU hr
      ⟨hAnn.1.le, hAnn.2.le⟩ hComp hpA hqA hwA
    have hOne : d ((2 : ℝ)^(-j) • w) = 1 := by
      dsimp only [d, comparableRadialThirdProfile]
      rw [zpow_neg, comparableThirdSchwartzProfile_scaled,
        comparableThirdCutoff_eq_one (comparableLower_pos κ L U hκ hL hU)
          ((comparableLower_pos κ L U hκ hL hU).trans_le (comparableLower_le_upper κ L U)) hr band.2.2,
        Complex.ofReal_one]
    have hK := (hShift A p q j hj hComp hpA hqA hwA).2.1
    change (∑ k ∈ I, integerRadialWindow (j+k) p) = 1 at hK
    simp only [F, hOne, mul_one, ← Finset.sum_mul, ← Complex.ofReal_sum]
    rw [hK, Complex.ofReal_one, one_mul]
  have hOne := (integerRadialWindow_hasSum q).tsum_eq
  rw [if_neg hq, tsum_eq_sum hQ] at hOne
  simp_rw [same, hF]
  rw [Finset.sum_comm]
  simp_rw [perHigh]
  rw [← Complex.ofReal_sum, hOne, Complex.ofReal_one]

end Burnett.A05
