import Burnett.Analysis.AngularCaps.UniformNullCharts

set_option autoImplicit false
set_option maxHeartbeats 5400000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set
open scoped BigOperators

def freeAxes (i j : Index) : Finset Index := (Finset.univ.erase i).erase j

theorem freeAxes_card {i j : Index} (hji : j ≠ i) : (freeAxes i j).card = 2 := by
  have hj : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
  rw [freeAxes, Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ i),
    Finset.card_univ, Fintype.card_fin]

def transverseSide (a : ℝ) (s : Bool) (t : ℝ) : Prop :=
  if s then a ≤ -t else a ≤ t

def nullSector (m : Form) (i j : Index) (s : Bool) (a : ℝ) : Set Vec :=
  {x | x ∈ chartBox i ∧ quadratic m x = 0 ∧ transverseSide a s (rowValue m x j)}

theorem exists_transverseSide {a t : ℝ} (h : a ≤ |t|) : ∃ s : Bool, transverseSide a s t := by
  by_cases ht : 0 ≤ t
  · exact ⟨false, by simpa only [transverseSide, Bool.false_eq_true, if_false, abs_of_nonneg ht] using h⟩
  · exact ⟨true, by simpa only [transverseSide, if_true, abs_of_nonpos (le_of_not_ge ht)] using h⟩

theorem sum_abs_lower_of_transverseSide {a u v : ℝ} (ha : 0 < a) {s : Bool}
    (hu : transverseSide a s u) (hv : transverseSide a s v) : 2*a ≤ |u+v| := by
  cases s with
  | false =>
    change a ≤ u at hu
    change a ≤ v at hv
    rw [abs_of_nonneg (by linarith)]
    linarith
  | true =>
    change a ≤ -u at hu
    change a ≤ -v at hv
    rw [abs_of_nonpos (by linarith)]
    linarith

/-- In one axis and derivative-sign chart, true null points form a
quantitative graph over the two remaining affine coordinates. -/
theorem nullSector_unitRep_dist_le {m : Form} (hm : Symmetric m)
    {i j : Index} (hji : j ≠ i) {s : Bool} {a B ε : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hε : 0 ≤ ε) {x y : Vec}
    (hx : x ∈ nullSector m i j s a) (hy : y ∈ nullSector m i j s a)
    (hBX : ∀ k, |rowValue m x k| ≤ B) (hBY : ∀ k, |rowValue m y k| ≤ B)
    (hclose : ∀ k ∈ freeAxes i j, |x k-y k| ≤ ε) :
    dist (unitRep x) (unitRep y) ≤ (4*(1+2*B/a))*ε := by
  let f (k : Index) := (rowValue m x k + rowValue m y k)*(x k-y k)
  have hF : (∑ k, f k) = 0 := by
    rw [← quadratic_sub_eq_rowSum hm x y, hx.2.1, hy.2.1, sub_self]
  have hI : f i = 0 := by
    simp only [f, hx.1.1, hy.1.1, sub_self, mul_zero]
  have hJmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hAbs : |f j| ≤ ∑ k ∈ freeAxes i j, |f k| := by
    rw [← Finset.sum_erase_add Finset.univ f (Finset.mem_univ i), hI, add_zero] at hF
    rw [← Finset.sum_erase_add (Finset.univ.erase i) f hJmem] at hF
    have hEq : f j = -(∑ k ∈ freeAxes i j, f k) := by
      dsimp only [freeAxes]
      linarith only [hF]
    rw [hEq, abs_neg]
    exact Finset.abs_sum_le_sum_abs _ _
  have hLower : 2*a * |x j-y j| ≤ |f j| := by
    rw [show |f j| = |rowValue m x j+rowValue m y j| * |x j-y j| from abs_mul _ _]
    exact mul_le_mul_of_nonneg_right (sum_abs_lower_of_transverseSide ha hx.2.2 hy.2.2) (abs_nonneg _)
  have hUpper : (∑ k ∈ freeAxes i j, |f k|) ≤ 4*B*ε := by
    calc
      _ ≤ ∑ _ ∈ freeAxes i j, (2*B)*ε := by
        refine Finset.sum_le_sum fun k hk => ?_
        rw [show |f k| = |rowValue m x k+rowValue m y k| * |x k-y k| from abs_mul _ _]
        have hRow : |rowValue m x k+rowValue m y k| ≤ 2*B :=
          (abs_add_le _ _).trans ((add_le_add (hBX k) (hBY k)).trans_eq (two_mul _).symm)
        exact mul_le_mul hRow (hclose k hk) (abs_nonneg _) (mul_nonneg zero_le_two hB)
      _ = _ := by
        simp only [Finset.sum_const, freeAxes_card hji, nsmul_eq_mul, Nat.cast_ofNat]
        ring
  have hCoordJ : |x j-y j| ≤ (2*B/a)*ε := by
    have h0 : 0 < 2*a := mul_pos (by norm_num) ha
    have h := (le_div_iff₀ h0).mpr
      ((mul_comm |x j-y j| (2*a)).le.trans (hLower.trans (hAbs.trans hUpper)))
    have hEq : 4*B*ε/(2*a) = (2*B/a)*ε := by
      field_simp [ha.ne']
      ring
    exact h.trans_eq hEq
  have hFactor : 0 ≤ 2*B/a := div_nonneg (mul_nonneg zero_le_two hB) ha.le
  have hAll (k : Index) : |(x-y) k| ≤ (1+2*B/a)*ε := by
    change |x k-y k| ≤ _
    by_cases hki : k=i
    · rw [hki, hx.1.1, hy.1.1, sub_self, abs_zero]
      exact mul_nonneg (add_nonneg zero_le_one hFactor) hε
    by_cases hkj : k=j
    · rw [hkj]
      exact hCoordJ.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) hε)
    have hk : k ∈ freeAxes i j :=
      Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ _⟩⟩
    exact (hclose k hk).trans ((one_mul ε).symm.le.trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hFactor) hε))
  have hN := norm_le_twice_of_coordinates (x-y) ((1+2*B/a)*ε)
    (mul_nonneg (add_nonneg zero_le_one hFactor) hε) hAll
  calc
    _ ≤ 2*dist x y := unitRep_dist_le (norm_at_least_one_of_chartBox hx.1) (norm_at_least_one_of_chartBox hy.1)
    _ ≤ 2*(2*((1+2*B/a)*ε)) := by
      rw [dist_eq_norm]
      exact mul_le_mul_of_nonneg_left hN zero_le_two
    _ = _ := by ring

end Burnett.Analysis.ProjectiveNullCaps
