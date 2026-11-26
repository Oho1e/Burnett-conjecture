import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicWindows
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit Finset
open scoped BigOperators

/-- The local square error from the remote physical convolution is summable
over precisely the consecutive or nonconsecutive dyadic scales in the ball. -/
theorem coefficientWindow_square_ratios_sum_le (J : Finset ℕ) {t R : ℝ}
    (ht : 0<t) (hR : 0<R) (hs : ∀ j ∈ J, dyadicScale t j ≤ R) :
    (∑ j ∈ J, (dyadicScale t j/R)^2) ≤ 2 := by
  obtain hEmpty | hNonempty := J.eq_empty_or_nonempty
  · simp [hEmpty]
  let k := J.max' hNonempty
  have hk := hs k (J.max'_mem hNonempty)
  have sub : J ⊆ range (k+1) := fun j hj => mem_range.mpr (Nat.lt_succ_of_le (J.le_max' j hj))
  have for_range (j : ℕ) (hj : j ∈ range (k+1)) : (dyadicScale t j/R)^2 ≤ ((1 : ℝ)/2)^(k-j) := by
    have hjk := Nat.le_of_lt_succ (mem_range.mp hj)
    have he : dyadicScale t j = ((1 : ℝ)/2)^(k-j)*dyadicScale t k := by
      simp only [dyadicScale,one_div,inv_pow]
      rw [← Nat.sub_add_cancel hjk,pow_add]
      field_simp
      simp
    have bound : dyadicScale t j/R ≤ ((1 : ℝ)/2)^(k-j) := by
      rw [div_le_iff₀ hR,he]
      gcongr
    have hx : 0≤dyadicScale t j/R := by unfold dyadicScale; positivity
    have hb : ((1 : ℝ)/2)^(k-j) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    exact (show (dyadicScale t j/R)^2 ≤ dyadicScale t j/R from
      by nlinarith only [mul_nonneg hx (sub_nonneg.mpr (bound.trans hb))]).trans bound
  calc
    _ ≤ ∑ j ∈ range (k+1), (dyadicScale t j/R)^2 :=
      sum_le_sum_of_subset_of_nonneg sub fun _ _ _ => sq_nonneg _
    _ ≤ ∑ j ∈ range (k+1), ((1 : ℝ)/2)^(k-j) := sum_le_sum for_range
    _ = ∑ j ∈ range (k+1), ((1 : ℝ)/2)^j := by
      simpa only [Nat.add_sub_cancel] using sum_range_reflect (fun j => ((1 : ℝ)/2)^j) (k+1)
    _ ≤ 2 := sum_geometric_two_le (k+1)

end Burnett.A06
