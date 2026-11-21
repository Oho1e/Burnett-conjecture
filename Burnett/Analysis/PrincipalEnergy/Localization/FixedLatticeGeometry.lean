import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Metric
open scoped BigOperators

abbrev LatticeIndex := Fin 4 → ℤ
abbrev LatticeSpace := EuclideanSpace ℝ (Fin 4)

def latticeCenter (a : LatticeIndex) : LatticeSpace := WithLp.toLp 2 fun j => (a j : ℝ)

def latticeNear (a b : LatticeIndex) : Prop := ∀ j, |a j - b j| ≤ 8

instance (a b : LatticeIndex) : Decidable (latticeNear a b) := by
  unfold latticeNear
  infer_instance

theorem latticeNear_symm {a b : LatticeIndex} (h : latticeNear a b) : latticeNear b a := by
  intro j
  rw [abs_sub_comm]
  exact h j

private theorem lattice_norm_le_of_coordinate (x : LatticeSpace) (d : ℝ) (hd : 0 ≤ d)
    (h : ∀ j, ‖x j‖ ≤ d) : ‖x‖ ≤ 2 * d := by
  rw [EuclideanSpace.norm_eq]
  apply (Real.sqrt_le_left (by positivity : 0 ≤ 2 * d)).2
  calc
    (∑ j, ‖x j‖ ^ 2) ≤ ∑ _ : Fin 4, d ^ 2 := by
      exact Finset.sum_le_sum fun j _ => pow_le_pow_left₀ (norm_nonneg _) (h j) 2
    _ = (2 * d) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

/-- The fixed radius-three open balls around the integer lattice cover all
four-dimensional Euclidean space. -/
theorem lattice_ball_cover : (⋃ a : LatticeIndex, ball (latticeCenter a) 3) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro x
  let a : LatticeIndex := fun j => Int.floor (x j)
  have hnorm : ‖x - latticeCenter a‖ ≤ 2 * 1 := by
    apply lattice_norm_le_of_coordinate _ _ (by norm_num)
    intro j
    change ‖x j - (a j : ℝ)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr (Int.floor_le (x j)))]
    change Int.fract (x j) ≤ 1
    exact (Int.fract_lt_one (x j)).le
  apply Set.mem_iUnion.mpr
  refine ⟨a, ?_⟩
  rw [mem_ball, dist_eq_norm]
  linarith

/-- The two radius-three supported cutoffs of a near pair fit into a single
radius-nineteen closed ball at the first center. -/
theorem lattice_pair_plateau {a b : LatticeIndex} (h : latticeNear a b) :
    closedBall (latticeCenter a) 3 ∪ closedBall (latticeCenter b) 3 ⊆
      closedBall (latticeCenter a) 19 := by
  have hab : dist (latticeCenter b) (latticeCenter a) ≤ 2 * 8 := by
    rw [dist_eq_norm]
    apply lattice_norm_le_of_coordinate _ _ (by norm_num)
    intro j
    change ‖(b j : ℝ) - (a j : ℝ)‖ ≤ 8
    rw [Real.norm_eq_abs]
    exact_mod_cast latticeNear_symm h j
  intro x hx
  rcases hx with hx | hx
  · exact closedBall_subset_closedBall (by norm_num) hx
  · rw [mem_closedBall] at hx ⊢
    have ht := dist_triangle x (latticeCenter b) (latticeCenter a)
    linarith

/-- Every far pair of those supported cutoffs has a uniform positive distance. -/
theorem lattice_pair_separated {a b : LatticeIndex} (h : ¬latticeNear a b) {x y : LatticeSpace}
    (hx : x ∈ closedBall (latticeCenter a) 3) (hy : y ∈ closedBall (latticeCenter b) 3) :
    1 ≤ ‖x-y‖ := by
  unfold latticeNear at h
  push_neg at h
  obtain ⟨j, hj⟩ := h
  have hdiff : (9 : ℤ) ≤ |a j - b j| := by omega
  have hcenters : (9 : ℝ) ≤ dist (latticeCenter a) (latticeCenter b) := by
    calc
      _ ≤ |(a j : ℝ) - (b j : ℝ)| := by exact_mod_cast hdiff
      _ = dist ((latticeCenter a) j) ((latticeCenter b) j) := (Real.dist_eq _ _).symm
      _ ≤ _ := PiLp.dist_apply_le _ _ j
  rw [mem_closedBall] at hx hy
  rw [← dist_eq_norm]
  have hfirst := dist_triangle (latticeCenter a) x (latticeCenter b)
  have hnext := dist_triangle x y (latticeCenter b)
  rw [dist_comm (latticeCenter a) x] at hfirst
  linarith

/-- Restricting a lattice neighborhood to any finite subset preserves a
single cardinal bound independent of its location or size. -/
theorem lattice_pair_degree (s : Finset LatticeIndex) (a : LatticeIndex) :
    (s.filter fun b => latticeNear a b).card ≤ 17 ^ 4 := by
  classical
  let N := s.filter fun b => latticeNear a b
  have hb (b : N) (j : Fin 4) : |b.val j - a j| ≤ 8 :=
    latticeNear_symm (Finset.mem_filter.mp b.property).2 j
  let offset (b : N) (j : Fin 4) : Fin 17 :=
    ⟨(b.val j - a j + 8).toNat, by
      obtain ⟨hl, hu⟩ := abs_le.mp (hb b j)
      omega⟩
  have hInj : Function.Injective offset := by
    intro b c eq
    apply Subtype.ext
    funext j
    have h := congrArg (fun f : Fin 4 → Fin 17 => (f j).val) eq
    change (b.val j - a j + 8).toNat = (c.val j - a j + 8).toNat at h
    have hbL := (abs_le.mp (hb b j)).1
    have hcL := (abs_le.mp (hb c j)).1
    omega
  have h := Fintype.card_le_of_injective offset hInj
  simpa [N, Fintype.card_fun] using h

end Burnett.Analysis.CarlesonEmbedding
