import Burnett.Analysis.AngularCaps.NullChartGraph
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set
open scoped BigOperators

def gridCoordinate (N : ℕ) (t : ℝ) (ht : |t| ≤ 1) : Fin (2*N+1) :=
  ⟨Nat.floor ((N:ℝ)*(t+1)), by
    have h : t+1 ≤ 2 := by linarith only [(abs_le.mp ht).2]
    have h' : (N:ℝ)*(t+1) ≤ ((2*N : ℕ):ℝ) := by
      push_cast
      exact (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)
    exact Nat.lt_succ_of_le (Nat.floor_le_of_le h')⟩

theorem gridCoordinate_abs_sub_le {N : ℕ} (hN : 0 < N) {t u : ℝ}
    (ht : |t| ≤ 1) (hu : |u| ≤ 1) (hEq : gridCoordinate N t ht = gridCoordinate N u hu) :
    |t-u| ≤ (N:ℝ)⁻¹ := by
  have hFloor : Nat.floor ((N:ℝ)*(t+1)) = Nat.floor ((N:ℝ)*(u+1)) := congrArg Fin.val hEq
  have ht₀ : 0 ≤ t+1 := by linarith only [(abs_le.mp ht).1]
  have hu₀ : 0 ≤ u+1 := by linarith only [(abs_le.mp hu).1]
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have htl := Nat.floor_le (mul_nonneg hn.le ht₀)
  have hul := Nat.floor_le (mul_nonneg hn.le hu₀)
  have htu := Nat.lt_floor_add_one ((N:ℝ)*(t+1))
  have huu := Nat.lt_floor_add_one ((N:ℝ)*(u+1))
  rw [hFloor] at htl htu
  have hDiff : |(N:ℝ)*(t-u)| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith only [htl, hul, htu, huu]
  rw [abs_mul, abs_of_pos hn] at hDiff
  rw [← one_div]
  exact (le_div_iff₀ hn).mpr (by rwa [mul_comm])

abbrev AxisChoice := {p : Index × Index // p.2 ≠ p.1}

abbrev GridLabel (N : ℕ) :=
  Σ p : AxisChoice, Bool × (↥(freeAxes p.1.1 p.1.2) → Fin (2*N+1))

theorem gridLabel_card_le (N : ℕ) : Fintype.card (GridLabel N) ≤ 32*(2*N+1)^2 := by
  classical
  have hAxis : Fintype.card AxisChoice ≤ 16 := by
    simpa only [Fintype.card_prod, Fintype.card_fin] using
      (Fintype.card_subtype_le (fun p : Index × Index => p.2 ≠ p.1))
  have hBlock (p : AxisChoice) :
      Fintype.card (Bool × (↥(freeAxes p.1.1 p.1.2) → Fin (2*N+1))) = 2*(2*N+1)^2 := by
    rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_fun, Fintype.card_coe, freeAxes_card p.2,
      Fintype.card_fin]
  rw [Fintype.card_sigma]
  simp only [hBlock, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact (Nat.mul_le_mul_right (2*(2*N+1)^2) hAxis).trans_eq (by ring)

def inNullGridCell (m : Form) (a : ℝ) {N : ℕ} (l : GridLabel N) (x : Vec) : Prop :=
  ∃ hx : x ∈ nullSector m l.1.1.1 l.1.1.2 l.2.1 a,
    ∀ k : ↥(freeAxes l.1.1.1 l.1.1.2), gridCoordinate N (x k.val) (hx.1.2 k.val) = l.2.2 k

theorem exists_gridLabel_of_sector {m : Form} {a : ℝ} (N : ℕ)
    {p : AxisChoice} {s : Bool} {x : Vec}
    (hx : x ∈ nullSector m p.1.1 p.1.2 s a) :
    ∃ l : GridLabel N, inNullGridCell m a l x :=
  ⟨⟨p, s, fun k => gridCoordinate N (x k.val) (hx.1.2 k.val)⟩, hx, fun _ => rfl⟩

theorem inNullGridCell_rep_dist_le {m : Form} (hm : Symmetric m)
    {N : ℕ} (hN : 0 < N) {a B : ℝ} (ha : 0 < a) (hB : 0 ≤ B)
    (hUpper : ∀ x : Vec, ‖x‖ ≤ 2 → ∀ k, |rowValue m x k| ≤ B)
    {l : GridLabel N} {x y : Vec} (hx : inNullGridCell m a l x) (hy : inNullGridCell m a l y) :
    dist (unitRep x) (unitRep y) ≤ (4*(1+2*B/a))*(N:ℝ)⁻¹ := by
  obtain ⟨hx, hcellX⟩ := hx
  obtain ⟨hy, hcellY⟩ := hy
  refine nullSector_unitRep_dist_le hm l.1.2 ha hB (inv_nonneg.mpr (Nat.cast_nonneg _)) hx hy
    (hUpper x (by simpa only [mul_one] using norm_le_twice_of_coordinates x 1 zero_le_one hx.1.2))
    (hUpper y (by simpa only [mul_one] using norm_le_twice_of_coordinates y 1 zero_le_one hy.1.2)) ?_
  intro k hk
  exact gridCoordinate_abs_sub_le hN (hx.1.2 k) (hy.1.2 k) ((hcellX ⟨k,hk⟩).trans (hcellY ⟨k,hk⟩).symm)

end Burnett.Analysis.ProjectiveNullCaps
