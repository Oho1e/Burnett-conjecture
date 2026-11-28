import Burnett.Analysis.TransportWard.Weyl.EulerJetBounds
import Burnett.Analysis.TransportWard.Weyl.CompactMetricCoefficientBounds

/-! The lower Euler estimates with the coefficient derivative bounds discharged
by one compact field range. -/

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.V03

open Set Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

/-- A single constant controls the three lower-product classes for all indices
and all segments inside one compact nonsingular field range. -/
theorem exists_metricEulerJetLowerRemainder_uniform_bounds {ι : Type*} [Fintype ι] (S : ι → Mat)
    {K : Set Mat} (hK : IsCompact K) (hKdet : K ⊆ nonsingularMetricDomain) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g h : Mat) (p dp : ActionSlot ι → ℝ)
      (q : Fin 4 → ActionSlot ι → ℝ) (i : ι),
      (∀ u ∈ Icc (0 : ℝ) 1, fieldSegment g h u ∈ K) →
      ∀ {P H Q : ℝ}, (∀ s, ‖p s‖ ≤ P) → (∀ s, ‖dp s‖ ≤ H) → (∀ a t, ‖q a t‖ ≤ Q) →
      ‖metricEulerJetLowerRemainder S g h p dp q i‖ ≤
        ((Fintype.card (ActionSlot ι) : ℝ)^2) *
          (M * ‖h‖^3 * P^2 + 2 * (M * ‖h‖^2) * P * H + M * ‖h‖ * H^2) +
          (4 * (Fintype.card (ActionSlot ι) : ℝ)) * (M * ‖h‖^3 * Q) := by
  let C (j : ActionSlot ι × ActionSlot ι) := metricActionCoefficient S j.1 j.2
  let L (j : ι × ActionSlot ι × ActionSlot ι) := metricEulerLowerCoefficient S j.1 j.2.1 j.2.2
  obtain ⟨M₀, hM₀, hC⟩ := exists_field_family_derivative_bounds_on_compact C
    isOpen_nonsingularMetricDomain (fun j => contDiffOn_metricActionCoefficient S j.1 j.2) hK hKdet
  obtain ⟨M₁, hM₁, hL⟩ := exists_field_family_derivative_bounds_on_compact L
    isOpen_nonsingularMetricDomain
    (fun j => contDiffOn_metricEulerLowerCoefficient S j.1 j.2.1 j.2.2) hK hKdet
  refine ⟨M₀ + M₁, add_nonneg hM₀ hM₁, fun g h p dp q i hseg P H Q hP hH hQ => ?_⟩
  refine norm_metricEulerJetLowerRemainder_le S g h p dp q i
    (fun u hu => hKdet (hseg u hu)) hP hH hQ ?_ ?_ ?_ ?_
  · intro a t u hu
    calc
      _ ≤ M₀ * ‖h‖ * ‖h‖ * ‖h‖ := (hC ((a, i), t) _ (hseg u hu)).2.2 h h h
      _ = M₀ * ‖h‖^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  · intro s t u hu
    exact ((hL (i, s, t) _ (hseg u hu)).1).trans (by linarith)
  · intro s t u hu
    exact ((hL (i, s, t) _ (hseg u hu)).2.1).trans (by linarith)
  · intro s t u hu
    calc
      _ ≤ M₁ * ‖h‖ * ‖h‖ * ‖h‖ := (hL (i, s, t) _ (hseg u hu)).2.2 h h h
      _ = M₁ * ‖h‖^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) (by positivity)

end Burnett.V03
