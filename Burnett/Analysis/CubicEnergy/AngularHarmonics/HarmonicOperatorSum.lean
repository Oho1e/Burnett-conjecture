import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Topology.Algebra.InfiniteSum.Real

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open scoped BigOperators ENNReal

/-- The degree and within-degree index of a round three-sphere harmonic. -/
abbrev HarmonicMode := Σ l : ℕ, Fin ((l + 1) ^ 2)

private def cubicDecay (l : ℕ) : ℝ := 1 / ((l : ℝ) + 1) ^ 3

private theorem cubic_le_inverse_square_difference (x : ℝ) (hx : 0 < x) :
    1 / (x + 1) ^ 3 ≤ 1 / x ^ 2 - 1 / (x + 1) ^ 2 := by
  have hx1 : x + 1 ≠ 0 := by positivity
  rw [← sub_nonneg]
  calc
    1 / x ^ 2 - 1 / (x + 1) ^ 2 - 1 / (x + 1) ^ 3 =
        (x ^ 2 + 3 * x + 1) / (x ^ 2 * (x + 1) ^ 3) := by
      field_simp [hx.ne', hx1]
      ring
    _ ≥ 0 := by positivity

private theorem cubic_tail (L : ℕ) :
    Summable (fun n : ℕ => cubicDecay (n + (L + 1))) ∧
      (∑' n : ℕ, cubicDecay (n + (L + 1))) ≤ 1 / ((L : ℝ) + 1) ^ 2 := by
  let v (n : ℕ) : ℝ := 1 / ((n : ℝ) + ((L : ℝ) + 1)) ^ 2
  have bound (n : ℕ) :
      (∑ i ∈ Finset.range n, cubicDecay (i + (L + 1))) ≤
        1 / ((L : ℝ) + 1) ^ 2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range n, (v i - v (i + 1)) := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [cubicDecay, v, Nat.cast_add, Nat.cast_one,
          add_assoc, add_left_comm, add_comm] using
          (cubic_le_inverse_square_difference ((i : ℝ) + ((L : ℝ) + 1)) (by positivity))
      _ = v 0 - v n := Finset.sum_range_sub' v n
      _ ≤ _ := by
        have hn : 0 ≤ v n := by dsimp [v]; positivity
        simpa only [v, Nat.cast_zero, zero_add] using sub_le_self (v 0) hn
  have summable : Summable (fun n : ℕ => cubicDecay (n + (L + 1))) :=
    summable_of_sum_range_le (fun _ => by unfold cubicDecay; positivity) bound
  exact ⟨summable, summable.tsum_le_of_sum_range_le bound⟩

private theorem cubic_summable : Summable cubicDecay :=
  (summable_nat_add_iff 1).mp (cubic_tail 0).1

private theorem cubic_sum_le : (∑' l : ℕ, cubicDecay l) ≤ 2 := by
  rw [← cubic_summable.sum_add_tsum_nat_add 1, Finset.sum_range_one]
  have head : cubicDecay 0 = 1 := by norm_num [cubicDecay]
  have tail : (∑' n : ℕ, cubicDecay (n + 1)) ≤ 1 := by
    simpa using (cubic_tail 0).2
  linarith only [head, tail]

/-- Operator-norm control of the series, all finite selections, and the tail
after including every harmonic of degree at most `L`. -/
structure HarmonicOperatorSeriesEstimate {Z : Type*} [NormedAddCommGroup Z]
    (term : HarmonicMode → Z) (A : ℝ) : Prop where
  summable : Summable term
  absoluteSummable : Summable (fun i => ‖term i‖)
  absoluteSumBound : (∑' i, ‖term i‖) ≤ 2 * A
  fullBound : ‖∑' i, term i‖ ≤ 2 * A
  finiteBound : ∀ J : Finset HarmonicMode, ‖∑ i ∈ J, term i‖ ≤ 2 * A
  tailBound : ∀ L : ℕ,
    ‖(∑' i, term i) -
      ∑ l ∈ Finset.range (L + 1), ∑ k : Fin ((l + 1) ^ 2), term ⟨l, k⟩‖ ≤
        A / ((L : ℝ) + 1) ^ 2

theorem harmonic_series_estimate {Z : Type*} [NormedAddCommGroup Z] [CompleteSpace Z]
    (term : HarmonicMode → Z) {A : ℝ} (hA : 0 ≤ A)
    (hTerm : ∀ i, ‖term i‖ ≤ A / ((i.1 : ℝ) + 1) ^ 5) :
    HarmonicOperatorSeriesEstimate term A := by
  let degrees (l : ℕ) := ∑ k : Fin ((l + 1) ^ 2), term ⟨l, k⟩
  let absDegrees (l : ℕ) := ∑ k : Fin ((l + 1) ^ 2), ‖term ⟨l, k⟩‖
  have degreeBound (l : ℕ) : absDegrees l ≤ A * cubicDecay l := by
    have hBase : (l : ℝ) + 1 ≠ 0 := by positivity
    calc
      _ ≤ ∑ _k : Fin ((l + 1) ^ 2), A / ((l : ℝ) + 1) ^ 5 :=
        Finset.sum_le_sum (fun k _ => hTerm ⟨l, k⟩)
      _ = A * cubicDecay l := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, cubicDecay]
        push_cast
        field_simp [hBase]
  have absDegreeNonneg (l : ℕ) : 0 ≤ absDegrees l :=
    Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have absDegreeSummable : Summable absDegrees :=
    (cubic_summable.mul_left A).of_nonneg_of_le absDegreeNonneg degreeBound
  have absModeSummable : Summable (fun i : HarmonicMode => ‖term i‖) := by
    apply (summable_sigma_of_nonneg (fun i => norm_nonneg (term i))).mpr
    refine ⟨fun _ => (hasSum_fintype _).summable, ?_⟩
    simpa only [tsum_fintype, absDegrees] using absDegreeSummable
  have absBound : (∑' i, ‖term i‖) ≤ 2 * A := by
    calc
      _ = ∑' l, absDegrees l := by
        simpa only [tsum_fintype, absDegrees] using absModeSummable.tsum_sigma
      _ ≤ ∑' l, A * cubicDecay l :=
        absDegreeSummable.tsum_le_tsum degreeBound (cubic_summable.mul_left A)
      _ ≤ 2 * A := by
        rw [tsum_mul_left, mul_comm 2 A]
        exact mul_le_mul_of_nonneg_left cubic_sum_le hA
  have modeSummable := absModeSummable.of_norm
  refine ⟨modeSummable, absModeSummable, absBound,
    (norm_tsum_le_tsum_norm absModeSummable).trans absBound, ?_, ?_⟩
  · intro J
    exact (norm_sum_le _ _).trans
      ((absModeSummable.sum_le_tsum J (fun _ _ => norm_nonneg _)).trans absBound)
  · intro L
    have degreeNorm (l : ℕ) : ‖degrees l‖ ≤ A * cubicDecay l :=
      (norm_sum_le _ _).trans (degreeBound l)
    have degreeSummable : Summable degrees :=
      (cubic_summable.mul_left A).of_norm_bounded degreeNorm
    have total : (∑' i, term i) = ∑' l, degrees l := by
      simpa only [tsum_fintype, degrees] using modeSummable.tsum_sigma
    have split := degreeSummable.sum_add_tsum_nat_add (L + 1)
    have shift := (cubic_tail L).1.mul_left A
    have absShift : Summable (fun n : ℕ => ‖degrees (n + (L + 1))‖) :=
      shift.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => degreeNorm (n + (L + 1)))
    rw [total, ← split, add_sub_cancel_left]
    calc
      _ ≤ ∑' n : ℕ, ‖degrees (n + (L + 1))‖ := norm_tsum_le_tsum_norm absShift
      _ ≤ ∑' n : ℕ, A * cubicDecay (n + (L + 1)) :=
        absShift.tsum_le_tsum (fun n => degreeNorm (n + (L + 1))) shift
      _ ≤ _ := by
        rw [tsum_mul_left, ← mul_one_div]
        exact mul_le_mul_of_nonneg_left (cubic_tail L).2 hA

abbrev CorrectionLp (p : ℝ≥0∞) :=
  Lp ℂ p (volume : Measure (EuclideanSpace ℝ (Fin 4)))

local instance correctionLpFour : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance correctionLpTwo : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance correctionLpFourThirds : Fact (1 ≤ ENNReal.ofReal (4 / 3 : ℝ)) :=
  ⟨by
    rw [← ENNReal.ofReal_one, ENNReal.ofReal_le_ofReal_iff (by norm_num)]
    norm_num⟩

abbrev HarmonicCorrectionOperator (r s : ℝ≥0∞) [Fact (1 ≤ r)] [Fact (1 ≤ s)] :=
  CorrectionLp 4 →L[ℂ] CorrectionLp r →L[ℂ] CorrectionLp s

/-- Combine the given harmonic coefficient and low-slot multiplier bounds with
the two fixed Cartesian operator bounds. The same low-slot maps and majorant
control both sums. -/
theorem harmonic_correction_operator_series
    (R : HarmonicMode → CorrectionLp 4 →L[ℂ] CorrectionLp 4)
    (B₁ : HarmonicMode → HarmonicCorrectionOperator 4 2)
    (B₂ : HarmonicMode → HarmonicCorrectionOperator 2 (ENNReal.ofReal (4 / 3 : ℝ)))
    (coefficientNorm : HarmonicMode → ℝ)
    {MNorm Ccoeff Cmult C₁ C₂ : ℝ} (hM : 0 ≤ MNorm)
    (hCcoeff : 0 ≤ Ccoeff) (hCmult : 0 ≤ Cmult) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hCoeff : ∀ i, coefficientNorm i ≤ Ccoeff * MNorm / ((i.1 : ℝ) + 1) ^ 12)
    (hR : ∀ i, ‖R i‖ ≤ Cmult * ((i.1 : ℝ) + 1) ^ 7)
    (hB₁ : ∀ i, ‖B₁ i‖ ≤ C₁ * coefficientNorm i)
    (hB₂ : ∀ i, ‖B₂ i‖ ≤ C₂ * coefficientNorm i) :
    let A := max C₁ C₂ * Cmult * Ccoeff * MNorm
    HarmonicOperatorSeriesEstimate (fun i => (B₁ i).comp (R i)) A ∧
      HarmonicOperatorSeriesEstimate (fun i => (B₂ i).comp (R i)) A := by
  intro A
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have majorant {r s : ℝ≥0∞} [Fact (1 ≤ r)] [Fact (1 ≤ s)]
      (B : HarmonicMode → HarmonicCorrectionOperator r s) {C : ℝ}
      (hC : 0 ≤ C) (hMax : C ≤ max C₁ C₂)
      (hB : ∀ i, ‖B i‖ ≤ C * coefficientNorm i) (i : HarmonicMode) :
      ‖(B i).comp (R i)‖ ≤ A / ((i.1 : ℝ) + 1) ^ 5 := by
    let x : ℝ := (i.1 : ℝ) + 1
    have hx : 0 < x := by dsimp [x]; positivity
    have hCartesian : ‖B i‖ ≤ max C₁ C₂ * (Ccoeff * MNorm / x ^ 12) :=
      (hB i).trans ((mul_le_mul_of_nonneg_left (hCoeff i) hC).trans
        (mul_le_mul_of_nonneg_right hMax (by positivity)))
    calc
      ‖(B i).comp (R i)‖ ≤ ‖B i‖ * ‖R i‖ := (B i).opNorm_comp_le (R i)
      _ ≤ (max C₁ C₂ * (Ccoeff * MNorm / x ^ 12)) * (Cmult * x ^ 7) :=
        mul_le_mul hCartesian (hR i) (norm_nonneg (R i)) ((norm_nonneg (B i)).trans hCartesian)
      _ = A / x ^ 5 := by
        dsimp only [A]
        field_simp [hx.ne']
  exact ⟨harmonic_series_estimate _ hA (majorant B₁ hC₁ (le_max_left _ _) hB₁),
    harmonic_series_estimate _ hA (majorant B₂ hC₂ (le_max_right _ _) hB₂)⟩

end Burnett.A06
