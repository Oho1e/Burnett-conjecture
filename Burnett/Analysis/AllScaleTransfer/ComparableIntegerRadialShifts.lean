import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition
import Burnett.Analysis.AllScaleTransfer.ComparableThirdAnnulus
import Burnett.Analysis.AllScaleTransfer.LowRatioAnnularShifts

set_option autoImplicit false
set_option maxHeartbeats 3300000

noncomputable section

namespace Burnett.A05

open Set Finset
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.LowRatio
open scoped BigOperators

private theorem finite_shift_sum (u : E) (hu : u ≠ 0) (j : ℤ) (N : ℕ)
    (hOutside : ∀ s : ℤ, s ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      integerRadialWindow (j+s) u = 0) :
    (∑ s ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), integerRadialWindow (j+s) u) = 1 := by
  classical
  have hReindex := (Equiv.addLeft j).tsum_eq (fun i => integerRadialWindow i u)
  change (∑' s : ℤ, integerRadialWindow (j+s) u) = ∑' i : ℤ, integerRadialWindow i u at hReindex
  rw [tsum_eq_sum hOutside] at hReindex
  exact hReindex.trans ((integerRadialWindow_hasSum u).tsum_eq.trans (if_neg hu))

/-- On the actual comparable triad support the first and signed third
windows use a single fixed finite interval of shifts from the second
index. Their finite signed sums are both one. -/
theorem exists_comparable_integerRadialWindow_finiteShifts {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (κ L U : ℝ) (hκ : 0 < κ) (hκsmall : κ < 1/16) (hL : 0 < L) (hU : 0 < U) :
    ∃ N : ℕ, ∀ (A : E ≃L[ℝ] E) (p q : E) (j : ℤ),
      integerRadialWindow j q ≠ 0 →
      let w := -(p+q)
      comparableSlotWeight ϑ κ (A p) (A q) (A w) ≠ 0 →
      (L*‖p‖ ≤ ‖A p‖ ∧ ‖A p‖ ≤ U*‖p‖) →
      (L*‖q‖ ≤ ‖A q‖ ∧ ‖A q‖ ≤ U*‖q‖) →
      (L*‖w‖ ≤ ‖A w‖ ∧ ‖A w‖ ≤ U*‖w‖) →
      let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
      (∀ i : ℤ, i-j ∉ I → integerRadialWindow i p = 0 ∧ integerRadialWindow i w = 0) ∧
      (∑ s ∈ I, integerRadialWindow (j+s) p) = 1 ∧
      (∑ s ∈ I, integerRadialWindow (j+s) w) = 1 := by
  let a := comparableRadialLower κ L U
  let b := comparableRadialUpper κ L U
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hb : 0 ≤ b := (by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_uniform_annular_shift_bound (a/2) (2*b) (1/2) 2
    (by positivity) (by positivity) (by norm_num)
  refine ⟨N, ?_⟩
  intro A p q j hj w hComp hpA hqA hwA I
  let r : ℝ := (2 : ℝ)^j
  have hr : 0 < r := by dsimp only [r]; positivity
  have hAnn : r/2 < ‖q‖ ∧ ‖q‖ < 2*r := radialAnnularCutoff_nonzero hr hj
  have hq0 : 0 < ‖q‖ := (by positivity : 0 < r/2).trans hAnn.1
  have hRad : ‖p‖ ∈ Set.Icc (a*r) (b*r) ∧ ‖q‖ ∈ Set.Icc (a*r) (b*r) ∧
      ‖w‖ ∈ Set.Icc (a*r) (b*r) :=
    comparable_normalized_triad_annulus hCut hFlat A hκ hκsmall hL hU hr
      ⟨hAnn.1.le, hAnn.2.le⟩ hComp hpA hqA hwA
  have outside (u : E) (hu : ‖u‖ ∈ Set.Icc (a*r) (b*r))
      (i : ℤ) (hi : i-j ∉ I) : integerRadialWindow i u = 0 := by
    by_contra hWin
    have hWinAnn := radialAnnularCutoff_nonzero (by positivity : 0 < (2 : ℝ)^i) hWin
    have hRatioLo : a/2 ≤ ‖u‖/‖q‖ := (le_div_iff₀ hq0).2 (calc
      _ ≤ (a/2)*(2*r) := mul_le_mul_of_nonneg_left hAnn.2.le (by positivity)
      _ = a*r := by ring
      _ ≤ _ := hu.1)
    have hRatioHi : ‖u‖/‖q‖ ≤ 2*b := (div_le_iff₀ hq0).2 (calc
      _ ≤ b*r := hu.2
      _ = (2*b)*(r/2) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hAnn.1.le (by positivity))
    have half_scale (l : ℤ) : (1/2 : ℝ) * (2 : ℝ)^l = (2 : ℝ)^l / 2 := by ring
    have hLocal := hN i j ‖u‖ ‖q‖
      (by rw [half_scale]; exact hWinAnn.1.le) hWinAnn.2.le
      (by rw [half_scale]; exact hAnn.1.le) hAnn.2.le hRatioLo hRatioHi
    exact hi (Finset.mem_Icc.mpr hLocal)
  have first_out := outside p hRad.1
  have third_out := outside w hRad.2.2
  have hp : p ≠ 0 := norm_pos_iff.mp ((mul_pos ha hr).trans_le hRad.1.1)
  have hw : w ≠ 0 := norm_pos_iff.mp ((mul_pos ha hr).trans_le hRad.2.2.1)
  refine ⟨fun i hi => ⟨first_out i hi, third_out i hi⟩,
    finite_shift_sum p hp j N ?_, finite_shift_sum w hw j N ?_⟩
  · intro s hs
    exact first_out (j+s) (by simpa only [add_sub_cancel_left] using hs)
  · intro s hs
    exact third_out (j+s) (by simpa only [add_sub_cancel_left] using hs)

end Burnett.A05
