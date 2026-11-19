import Burnett.Analysis.ShiftedFourierWindow.RadialKernel

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.ShiftedFourierWindow
open Finset
open scoped BigOperators

private theorem geometric_image (I : Finset ℕ) (u : ℕ → ℕ) (hu : Set.InjOn u (↑I : Set ℕ)) :
    ∑ k ∈ I, (1/2:ℝ)^(u k) ≤ 2 := by
  classical
  rw [← sum_image (f := fun n : ℕ => (1/2:ℝ)^n) hu]
  exact (summable_geometric_two.sum_le_tsum _ (fun _ _ => by positivity)).trans_eq tsum_geometric_two

private theorem relative_scale (t : ℝ) {k l : ℕ} (h : k ≤ l) :
    (1/2:ℝ)^(l-k) * ((2:ℝ)^l*t) = (2:ℝ)^k*t := by
  have hp : (2:ℝ)^l = (2:ℝ)^(l-k) * (2:ℝ)^k := by rw [← pow_add,Nat.sub_add_cancel h]
  rw [one_div_pow,hp]
  field_simp

/-- Across any finite subset of dyadic scales, the sum of the smaller of
scale/distance and distance/scale is bounded independently of the endpoints. -/
theorem dyadic_difference_sum (I : Finset ℕ) (t d : ℝ) (ht : 0<t) (hd : 0<d) :
    ∑ k ∈ I, min (((2:ℝ)^k*t)/d) (d/((2:ℝ)^k*t)) ≤ 4 := by
  classical
  let r := fun k : ℕ => (2:ℝ)^k*t
  let w := fun k => min (r k/d) (d/r k)
  let L := I.filter (fun k => r k ≤ d)
  let H := I.filter (fun k => ¬ r k ≤ d)
  have pos (k : ℕ) : 0 < r k := mul_pos (by positivity) ht
  have left : ∑ k ∈ L, w k ≤ 2 := by
    by_cases he : L.Nonempty
    · let b := L.max' he
      have le_b (k) (hk : k ∈ L) : k ≤ b := le_max' _ _ hk
      have rb : r b ≤ d := (mem_filter.mp (show b ∈ L from max'_mem _ _)).2
      refine (sum_le_sum (g := fun k => (1/2:ℝ)^(b-k)) (fun k hk => ?_)).trans
        (geometric_image L (fun k => b-k) ?_)
      · refine (min_le_left _ _).trans ((div_le_iff₀ hd).mpr ?_)
        change (2:ℝ)^k*t ≤ (1/2:ℝ)^(b-k)*d
        rw [← relative_scale t (le_b k hk)]
        exact mul_le_mul_of_nonneg_left rb (by positivity)
      · intro i hi j hj h
        have := le_b i hi
        have := le_b j hj
        dsimp at h
        omega
    · simp [not_nonempty_iff_eq_empty.mp he]
  have right : ∑ k ∈ H, w k ≤ 2 := by
    by_cases he : H.Nonempty
    · let b := H.min' he
      have b_le (k) (hk : k ∈ H) : b ≤ k := min'_le _ _ hk
      have db : d ≤ r b := le_of_not_ge (mem_filter.mp (show b ∈ H from min'_mem _ _)).2
      refine (sum_le_sum (g := fun k => (1/2:ℝ)^(k-b)) (fun k hk => ?_)).trans
        (geometric_image H (fun k => k-b) ?_)
      · refine (min_le_right _ _).trans ((div_le_iff₀ (pos k)).mpr ?_)
        change d ≤ (1/2:ℝ)^(k-b) * ((2:ℝ)^k*t)
        rw [relative_scale t (b_le k hk)]
        exact db
      · intro i hi j hj h
        have := b_le i hi
        have := b_le j hj
        dsimp at h
        omega
    · simp [not_nonempty_iff_eq_empty.mp he]
  have split : (∑ k ∈ L, w k) + (∑ k ∈ H, w k) = ∑ k ∈ I, w k :=
    sum_filter_add_sum_filter_not I (fun k => r k ≤ d) w
  change (∑ k ∈ I, w k) ≤ 4
  linarith

end Burnett.Analysis.SignedFourierWindow
