import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set Filter
open scoped BigOperators

abbrev Index := Fin 4
abbrev Vec := EuclideanSpace ℝ Index
abbrev Form := Index → Index → ℝ

def rowValue (m : Form) (x : Vec) (j : Index) : ℝ := ∑ i, m i j * x i

def pairing (m : Form) (x y : Vec) : ℝ := ∑ j, rowValue m x j * y j

def quadratic (m : Form) (x : Vec) : ℝ := pairing m x x

def Symmetric (m : Form) : Prop := ∀ i j, m i j = m j i

def Nondegenerate (m : Form) : Prop := ∀ x : Vec, (∀ j, rowValue m x j = 0) → x = 0

def unitNull (m : Form) : Set Vec := {x | ‖x‖ = 1 ∧ quadratic m x = 0}

def chartBox (i : Index) : Set Vec := {x | x i = 1 ∧ ∀ j, |x j| ≤ 1}

@[simp] theorem rowValue_smul (m : Form) (t : ℝ) (x : Vec) (j : Index) :
    rowValue m (t • x) j = t * rowValue m x j := by
  simp only [rowValue, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

@[simp] theorem quadratic_smul (m : Form) (t : ℝ) (x : Vec) :
    quadratic m (t • x) = t^2*quadratic m x := by
  simp only [quadratic, pairing, rowValue_smul, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

theorem pairing_symm {m : Form} (hm : Symmetric m) (x y : Vec) :
    pairing m x y = pairing m y x := by
  simp only [pairing, rowValue, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by
    rw [hm j i]
    ring

theorem quadratic_sub_eq_rowSum {m : Form} (hm : Symmetric m) (x y : Vec) :
    quadratic m x - quadratic m y =
      ∑ k, (rowValue m x k + rowValue m y k) * (x k - y k) := by
  calc
    _ = pairing m x x - pairing m x y + (pairing m y x - pairing m y y) := by
      rw [pairing_symm hm x y]
      unfold quadratic
      ring
    _ = _ := by
      simp only [pairing, add_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib]
      ring

theorem norm_le_twice_of_coordinates (x : Vec) (a : ℝ) (ha : 0 ≤ a)
    (hx : ∀ j, |x j| ≤ a) : ‖x‖ ≤ 2*a := by
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg zero_le_two ha)).mp
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ _j : Index, a^2 := Finset.sum_le_sum fun j _ => by
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [Real.norm_eq_abs] using hx j) 2
    _ = _ := by simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]; ring

theorem norm_at_least_one_of_chartBox {i : Index} {x : Vec} (hx : x ∈ chartBox i) :
    1 ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x i
  simpa only [hx.1, norm_one] using h

def unitRep (x : Vec) : Vec := ‖x‖⁻¹ • x

theorem unitRep_mem_unitNull {m : Form} {x : Vec} (hx : 0 < ‖x‖) (hQ : quadratic m x = 0) :
    unitRep x ∈ unitNull m := by
  constructor
  · rw [unitRep, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx.le), inv_mul_cancel₀ hx.ne']
  · simp only [unitRep, quadratic_smul, hQ, mul_zero]

/-- Chordal distance after identifying the two signed lifts of a projective point. -/
def projectiveDist (x y : Vec) : ℝ := min ‖x-y‖ ‖x+y‖

theorem projectiveDist_comm (x y : Vec) : projectiveDist x y = projectiveDist y x := by
  rw [projectiveDist, projectiveDist, norm_sub_rev, add_comm]

@[simp] theorem projectiveDist_self (x : Vec) : projectiveDist x x = 0 := by
  simp [projectiveDist]

theorem projectiveDist_le_dist (x y : Vec) : projectiveDist x y ≤ dist x y := by
  simpa only [projectiveDist, dist_eq_norm] using (min_le_left ‖x-y‖ ‖x+y‖)

theorem projectiveDist_triangle (x y z : Vec) :
    projectiveDist x z ≤ projectiveDist x y + projectiveDist y z := by
  rcases le_total ‖x-y‖ ‖x+y‖ with hxy | hxy
  · rcases le_total ‖y-z‖ ‖y+z‖ with hyz | hyz
    · simp only [projectiveDist, min_eq_left hxy, min_eq_left hyz]
      apply (min_le_left _ _).trans
      rw [show x-z = (x-y)+(y-z) by abel]
      exact norm_add_le _ _
    · simp only [projectiveDist, min_eq_left hxy, min_eq_right hyz]
      apply (min_le_right _ _).trans
      rw [show x+z = (x-y)+(y+z) by abel]
      exact norm_add_le _ _
  · rcases le_total ‖y-z‖ ‖y+z‖ with hyz | hyz
    · simp only [projectiveDist, min_eq_right hxy, min_eq_left hyz]
      apply (min_le_right _ _).trans
      rw [show x+z = (x+y)-(y-z) by abel]
      exact norm_sub_le _ _
    · simp only [projectiveDist, min_eq_right hxy, min_eq_right hyz]
      apply (min_le_left _ _).trans
      rw [show x-z = (x+y)-(y+z) by abel]
      exact norm_sub_le _ _

theorem unitRep_dist_le {x y : Vec} (hx : 1 ≤ ‖x‖) (hy : 1 ≤ ‖y‖) :
    dist (unitRep x) (unitRep y) ≤ 2 * dist x y := by
  have hx₀ : 0 < ‖x‖ := zero_lt_one.trans_le hx
  have hy₀ : 0 < ‖y‖ := zero_lt_one.trans_le hy
  have hd : |‖x‖ - ‖y‖| ≤ ‖x-y‖ := abs_norm_sub_norm_le _ _
  have hRecip : |‖x‖⁻¹ - ‖y‖⁻¹| * ‖y‖ = ‖x‖⁻¹ * |‖x‖ - ‖y‖| := by
    calc
      _ = |(‖x‖⁻¹ - ‖y‖⁻¹)*‖y‖| := by rw [abs_mul, abs_of_nonneg hy₀.le]
      _ = _ := by
        have hId : (‖x‖⁻¹ - ‖y‖⁻¹)*‖y‖ = -(‖x‖⁻¹ * (‖x‖-‖y‖)) := by
          field_simp [hx₀.ne', hy₀.ne']
          ring
        rw [hId, abs_neg, abs_mul, abs_of_nonneg (inv_nonneg.mpr hx₀.le)]
  rw [dist_eq_norm, dist_eq_norm, unitRep, unitRep,
    show ‖x‖⁻¹ • x - ‖y‖⁻¹ • y =
      ‖x‖⁻¹ • (x-y) + (‖x‖⁻¹-‖y‖⁻¹) • y by module]
  calc
    _ ≤ ‖‖x‖⁻¹ • (x-y)‖ + ‖(‖x‖⁻¹-‖y‖⁻¹) • y‖ := norm_add_le _ _
    _ = ‖x‖⁻¹*‖x-y‖ + ‖x‖⁻¹*|‖x‖-‖y‖| := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hx₀.le), Real.norm_eq_abs, hRecip]
    _ ≤ ‖x-y‖ + ‖x-y‖ := by
      exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) (inv_le_one_of_one_le₀ hx))
        (mul_le_of_le_one_left (abs_nonneg _) (inv_le_one_of_one_le₀ hx) |>.trans hd)
    _ = _ := (two_mul _).symm

theorem exists_projective_chart {m : Form} {v : Vec} (hv : v ∈ unitNull m) :
    ∃ i : Index, ∃ x : Vec, x ∈ chartBox i ∧ quadratic m x = 0 ∧
      projectiveDist v (unitRep x) = 0 := by
  classical
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ (fun j : Index => |v j|) Finset.univ_nonempty
  have hvi : v i ≠ 0 := by
    intro hi0
    have hz : v = 0 := by
      ext j
      have hj := hi j (Finset.mem_univ j)
      rw [hi0, abs_zero] at hj
      exact abs_nonpos_iff.mp hj
    have := hv.1
    rw [hz, norm_zero] at this
    norm_num at this
  let x := (v i)⁻¹ • v
  have hx : x ∈ chartBox i := by
    constructor
    · change (v i)⁻¹ * v i = 1
      exact inv_mul_cancel₀ hvi
    · intro j
      change |(v i)⁻¹*v j| ≤ 1
      rw [abs_mul, abs_inv]
      exact (mul_le_mul_of_nonneg_left (hi j (Finset.mem_univ j)) (inv_nonneg.mpr (abs_nonneg _))).trans_eq
        (inv_mul_cancel₀ (abs_ne_zero.mpr hvi))
  refine ⟨i, x, hx, by simp only [x, quadratic_smul, hv.2, mul_zero], ?_⟩
  have hn : ‖x‖ = |v i|⁻¹ := by
    rw [show x = (v i)⁻¹ • v from rfl, norm_smul, hv.1, mul_one, Real.norm_eq_abs, abs_inv]
  have hRep : unitRep x = (|v i| * (v i)⁻¹) • v := by
    rw [unitRep, hn, inv_inv]
    exact smul_smul _ _ _
  rcases lt_or_gt_of_ne hvi with hn | hp
  · rw [abs_of_neg hn, neg_mul, mul_inv_cancel₀ hvi, neg_one_smul] at hRep
    simp [hRep, projectiveDist, norm_nonneg]
  · rw [abs_of_pos hp, mul_inv_cancel₀ hvi, one_smul] at hRep
    simp [hRep]

end Burnett.Analysis.ProjectiveNullCaps
