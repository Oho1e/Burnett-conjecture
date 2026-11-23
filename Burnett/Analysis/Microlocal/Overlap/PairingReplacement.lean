import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter
open scoped Topology

/-- Strong replacement errors in both slots vanish in the pairing of one
fixed bounded operator on bounded input sequences. -/
theorem tendsto_orderedPairing_sub_of_strong_replacement
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (A : H →L[ℂ] H)
    (u₁ u₂ v₁ v₂ : ℕ → H) (C D : ℝ)
    (hC : ∀ n, ‖u₂ n‖ ≤ C) (hD : ∀ n, ‖v₁ n‖ ≤ D)
    (h₁ : Tendsto (fun n => u₁ n - v₁ n) atTop (𝓝 0))
    (h₂ : Tendsto (fun n => u₂ n - v₂ n) atTop (𝓝 0)) :
    Tendsto (fun n => inner ℂ (u₁ n) (A (u₂ n)) - inner ℂ (v₁ n) (A (v₂ n)))
      atTop (𝓝 0) := by
  have hLeft : Tendsto (fun n => inner ℂ (u₁ n - v₁ n) (A (u₂ n))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hLim : Tendsto (fun n => ‖u₁ n - v₁ n‖ * (‖A‖ * C)) atTop (𝓝 0) := by
      simpa only [norm_zero, zero_mul] using h₁.norm.mul_const (‖A‖ * C)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hLim
    exact (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left
      ((A.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC n) (norm_nonneg _))) (norm_nonneg _))
  have hRight : Tendsto (fun n => inner ℂ (v₁ n) (A (u₂ n - v₂ n))) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    have hLim : Tendsto (fun n => (D * ‖A‖) * ‖u₂ n - v₂ n‖) atTop (𝓝 0) := by
      simpa only [norm_zero, mul_zero] using h₂.norm.const_mul (D * ‖A‖)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hLim
    rw [mul_assoc]
    exact (norm_inner_le_norm _ _).trans
      (mul_le_mul (hD n) (A.le_opNorm _) (norm_nonneg _) ((norm_nonneg _).trans (hD n)))
  have hEq (n : ℕ) : inner ℂ (u₁ n) (A (u₂ n)) - inner ℂ (v₁ n) (A (v₂ n)) =
      inner ℂ (u₁ n - v₁ n) (A (u₂ n)) + inner ℂ (v₁ n) (A (u₂ n - v₂ n)) := by
    rw [inner_sub_left, map_sub, inner_sub_right]
    abel
  simp_rw [hEq]
  simpa only [add_zero] using hLeft.add hRight

end Burnett.Microlocal.Overlap
