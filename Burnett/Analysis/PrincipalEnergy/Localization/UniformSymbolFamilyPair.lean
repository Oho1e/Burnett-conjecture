import Mathlib.Analysis.Normed.Operator.BanachSteinhaus
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open BoundedContinuousFunction

private def singleBoundedSequence (n : ℕ) : ℕ →ᵇ ℝ :=
  ofNormedAddCommGroupDiscrete (fun m => if m = n then 1 else 0) 1
    (fun m => by by_cases h : m = n <;> simp [h])

private theorem singleBoundedSequence_norm_le (n : ℕ) : ‖singleBoundedSequence n‖ ≤ 1 := by
  apply (BoundedContinuousFunction.norm_le zero_le_one).mpr
  intro m
  change ‖(if m = n then (1 : ℝ) else 0)‖ ≤ 1
  by_cases h : m = n <;> simp [h]

/-- Uniform boundedness for a symbol family, expressed through the evaluations
on tests of its real geometrically weighted superpositions. For a fixed test,
the unweighted evaluations must already be bounded across centers. -/
theorem exists_uniform_symbol_family_bound_of_superpositions {ι T : Type*} (F : ι → T → ℂ)
    (hFixed : ∀ t, ∃ M : ℝ, ∀ i, ‖F i t‖ ≤ M)
    (hSuperposition : ∀ (i : ℕ → ι) (v : ℕ →ᵇ ℝ), ∃ M : ℝ, ∀ t,
      ‖∑' n, ((((1 : ℝ)/2)^n) * v n) • F (i n) t‖ ≤ M) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i t, ‖F i t‖ ≤ M := by
  by_contra! hUnbounded
  let w (n : ℕ) : ℝ := ((1 : ℝ)/2)^n
  have hw (n : ℕ) : 0 < w n := by dsimp [w]; positivity
  have hwS : Summable w := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  choose i t hBad using fun n : ℕ => hUnbounded ((n : ℝ)/w n) (by positivity)
  let V := ℕ →ᵇ ℝ
  let term (u : T) (n : ℕ) : V →L[ℝ] ℂ :=
    (BoundedContinuousFunction.evalCLM ℝ n).smulRight (w n • F (i n) u)
  have hTerm (u : T) : Summable (term u) := by
    obtain ⟨M, hM⟩ := hFixed u
    have hM₀ : 0 ≤ M := (norm_nonneg _).trans (hM (i 0))
    refine Summable.of_norm_bounded (f := term u) (hwS.mul_right M) fun n => ?_
    refine (term u n).opNorm_le_bound (mul_nonneg (hw n).le hM₀) fun v => ?_
    change ‖v n • (w n • F (i n) u)‖ ≤ w n * M * ‖v‖
    rw [norm_smul, norm_smul, Real.norm_of_nonneg (hw n).le]
    calc
      _ ≤ ‖v‖ * (w n * M) :=
        mul_le_mul (BoundedContinuousFunction.norm_coe_le_norm v n)
          (mul_le_mul_of_nonneg_left (hM _) (hw n).le) (by positivity) (norm_nonneg _)
      _ = _ := by ring
  let G (u : T) : V →L[ℝ] ℂ := ∑' n, term u n
  have hG (u : T) (v : V) : G u v = ∑' n, (w n * v n) • F (i n) u := by
    change (ContinuousLinearMap.apply ℝ ℂ v) (∑' n, term u n) = _
    rw [(ContinuousLinearMap.apply ℝ ℂ v).map_tsum (hTerm u)]
    apply tsum_congr
    intro n
    change v n • (w n • F (i n) u) = (w n * v n) • F (i n) u
    rw [smul_smul, mul_comm (v n)]
  obtain ⟨M, hM⟩ := banach_steinhaus (g := G) (fun v => by
    obtain ⟨B, hB⟩ := hSuperposition i v
    exact ⟨B, fun u => by rw [hG]; exact hB u⟩)
  obtain ⟨n, hn⟩ := exists_nat_gt M
  have hSingle : G (t n) (singleBoundedSequence n) = w n • F (i n) (t n) := by
    rw [hG, tsum_eq_single n]
    · change (w n * (if n=n then (1:ℝ) else 0)) • F (i n) (t n) = _
      rw [if_pos rfl, mul_one]
    · intro j hj
      change (w j * (if j=n then (1:ℝ) else 0)) • F (i j) (t n) = 0
      rw [if_neg hj, mul_zero, zero_smul]
  have hUpper : ‖G (t n) (singleBoundedSequence n)‖ ≤ M :=
    ((G (t n)).le_opNorm _).trans
      ((mul_le_mul_of_nonneg_left (singleBoundedSequence_norm_le n) (norm_nonneg _)).trans
        (by simpa only [mul_one] using hM (t n)))
  rw [hSingle, norm_smul, Real.norm_of_nonneg (hw n).le] at hUpper
  have hLower : (n : ℝ) < w n * ‖F (i n) (t n)‖ := by
    rw [mul_comm]
    exact (div_lt_iff₀ (hw n)).mp (hBad n)
  exact (not_lt_of_ge (hUpper.trans hn.le)) hLower

end Burnett.Analysis.CarlesonEmbedding
