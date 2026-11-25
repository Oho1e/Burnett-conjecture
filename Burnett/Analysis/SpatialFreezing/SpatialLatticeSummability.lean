import Burnett.Analysis.SpatialFreezing.FixedCubeFourier
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Ring.InfiniteSum

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped BigOperators

/-- The lattice weight used in the original mode coefficient bound. -/
def spatialLatticeWeight (k : Index → ℤ) : ℝ := 1 + ‖spatialLatticeVector k‖

private def coordinateWeight (n : ℤ) : ℝ := (1 + |(n : ℝ)|) ^ (-3 / 2 : ℝ)

private theorem coordinate_weight_nonneg (n : ℤ) : 0 ≤ coordinateWeight n := by
  unfold coordinateWeight
  positivity

private theorem summable_coordinate_weight : Summable coordinateWeight := by
  have base : Summable (fun n : ℕ => (n : ℝ) ^ (-3 / 2 : ℝ)) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  have shifted : Summable (fun n : ℕ => (1 + (n : ℝ)) ^ (-3 / 2 : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one, add_comm (1 : ℝ)] using (summable_nat_add_iff 1).2 base
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa only [coordinateWeight, Int.cast_natCast, Nat.abs_cast] using shifted
  · simpa only [coordinateWeight, Int.cast_neg, Int.cast_natCast, abs_neg, Nat.abs_cast] using shifted

private theorem summable_coordinate_product (m : ℕ) :
    Summable (fun k : Fin m → ℤ => ∏ j : Fin m, coordinateWeight (k j)) := by
  induction m with
  | zero => exact (hasSum_fintype _).summable
  | succ m ih =>
    let e := Fin.consEquiv (fun _ : Fin (m + 1) => ℤ)
    apply e.summable_iff.mp
    have hp := summable_coordinate_weight.mul_of_nonneg ih coordinate_weight_nonneg
      (fun _ => Finset.prod_nonneg (fun _ _ => coordinate_weight_nonneg _))
    simpa only [Function.comp_apply, Fin.prod_univ_succ, e, Fin.consEquiv,
      Equiv.coe_fn_mk, Fin.cons_zero, Fin.cons_succ] using hp

private theorem inv_weight_six_le_product (k : Index → ℤ) :
    (spatialLatticeWeight k ^ 6)⁻¹ ≤ ∏ j : Index, coordinateWeight (k j) := by
  let w := spatialLatticeWeight k
  have hw : 0 < w := by dsimp only [w, spatialLatticeWeight]; positivity
  have hCoord (j : Index) : 1 + |(k j : ℝ)| ≤ w := by
    apply add_le_add_left
    simpa only [spatialLatticeVector, Real.norm_eq_abs] using PiLp.norm_apply_le (spatialLatticeVector k) j
  have power : (w ^ 6)⁻¹ = ∏ _ : Index, w ^ (-3 / 2 : ℝ) := by
    rw [Finset.prod_const, Finset.card_univ]
    change (w ^ 6)⁻¹ = (w ^ (-3 / 2 : ℝ)) ^ (4 : ℕ)
    have exponent : (-3 / 2 : ℝ) * ((4 : ℕ) : ℝ) = -(6 : ℝ) := by norm_num
    rw [← Real.rpow_natCast (w ^ (-3 / 2 : ℝ)), ← Real.rpow_mul hw.le, exponent,
      Real.rpow_neg hw.le]
    norm_num
  change (w ^ 6)⁻¹ ≤ _
  rw [power]
  apply Finset.prod_le_prod
  · intro j _
    exact Real.rpow_nonneg hw.le _
  · intro j _
    exact Real.rpow_le_rpow_of_nonpos (by positivity) (hCoord j) (by norm_num)

private theorem summable_inverse_sixth_weight :
    Summable (fun k : Index → ℤ => (spatialLatticeWeight k ^ 6)⁻¹) :=
  Summable.of_nonneg_of_le (by intro k; unfold spatialLatticeWeight; positivity)
    inv_weight_six_le_product (summable_coordinate_product 4)

/-- The integer lattice mode weight is summable after multiplying by the
spatial derivative cost of order at most two when the decay exponent exceeds seven. -/
theorem summable_spatial_lattice_weighted_decay (L r : ℕ) (hL : 7 < L) (hr : r ≤ 2) :
    Summable (fun k : Index → ℤ => spatialLatticeWeight k ^ r / spatialLatticeWeight k ^ L) := by
  have hrL : r ≤ L := by omega
  have h6 : 6 ≤ L - r := by omega
  refine Summable.of_nonneg_of_le ?_ ?_ summable_inverse_sixth_weight
  · intro k
    unfold spatialLatticeWeight
    positivity
  · intro k
    let w := spatialLatticeWeight k
    have h1 : 1 ≤ w := le_add_of_nonneg_right (norm_nonneg _)
    have hn : w ^ r ≠ 0 := pow_ne_zero _ (by linarith)
    change w ^ r / w ^ L ≤ (w ^ 6)⁻¹
    have split : w ^ L = w ^ r * w ^ (L - r) := by rw [← pow_add, Nat.add_sub_of_le hrL]
    rw [split, div_mul_eq_div_div, div_self hn, one_div]
    exact inv_anti₀ (pow_pos (by linarith : 0 < w) _) (pow_le_pow_right₀ h1 h6)

/-- A single finite constant controls every mode truncation and every
derivative weight from zero through two. -/
theorem exists_spatial_lattice_weighted_truncation_bound (L : ℕ) (hL : 7 < L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : ℕ), r ≤ 2 → ∀ modes : Finset (Index → ℤ),
      ∑ k ∈ modes, spatialLatticeWeight k ^ r / spatialLatticeWeight k ^ L ≤ C := by
  let term (r : ℕ) (k : Index → ℤ) := spatialLatticeWeight k ^ r / spatialLatticeWeight k ^ L
  have positive (r : ℕ) (k : Index → ℤ) : 0 ≤ term r k := by
    unfold term spatialLatticeWeight
    positivity
  let C := ∑ r ∈ Finset.range 3, ∑' k, term r k
  refine ⟨C, Finset.sum_nonneg (fun r _ => tsum_nonneg (positive r)), ?_⟩
  intro r hr modes
  have h := summable_spatial_lattice_weighted_decay L r hL hr
  exact (h.sum_le_tsum modes (fun k _ => positive r k)).trans
    (Finset.single_le_sum (fun s _ => tsum_nonneg (positive s))
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hr)))

end Burnett.A03
