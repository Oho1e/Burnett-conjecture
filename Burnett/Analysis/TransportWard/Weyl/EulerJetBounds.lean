import Burnett.Analysis.FrozenTransport.V03EulerJetRemainder

/-! The three quantitative classes of the exact Euler jet remainder. -/

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 4000

noncomputable section

namespace Burnett.V03

open Set Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

private theorem norm_double_sum_le {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) {B : ℝ} (h : ∀ a b, ‖f a b‖ ≤ B) :
    ‖∑ a, ∑ b, f a b‖ ≤ (Fintype.card α : ℝ) * Fintype.card β * B := by
  calc
    _ ≤ ∑ a, ‖∑ b, f a b‖ := norm_sum_le _ _
    _ ≤ ∑ a : α, ∑ b : β, B :=
      Finset.sum_le_sum fun a _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun b _ => h a b)
    _ = _ := by simp [mul_assoc]

private theorem norm_quadratic_first_jet_sum_le (A B D p dp q dq : ℝ)
    {MA MB MD P H : ℝ} (hA : ‖A‖ ≤ MA) (hB : ‖B‖ ≤ MB) (hD : ‖D‖ ≤ MD)
    (hp : ‖p‖ ≤ P) (hq : ‖q‖ ≤ P) (hdp : ‖dp‖ ≤ H) (hdq : ‖dq‖ ≤ H) :
    ‖A * p * q + B * (dp * q + p * dq) + D * dp * dq‖ ≤
      MA * P^2 + 2 * MB * P * H + MD * H^2 := by
  have ht : ‖dp * q + p * dq‖ ≤ H * P + P * H :=
    (norm_add_le _ _).trans (by
      simp only [norm_mul]
      exact add_le_add (mul_le_mul hdp hq (norm_nonneg _) ((norm_nonneg _).trans hdp))
        (mul_le_mul hp hdq (norm_nonneg _) ((norm_nonneg _).trans hp)))
  calc
    _ ≤ ‖A * p * q‖ + ‖B * (dp * q + p * dq)‖ + ‖D * dp * dq‖ :=
      (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ MA * P * P + MB * (H * P + P * H) + MD * H * H := by
      simp only [norm_mul]
      apply add_le_add
      · apply add_le_add
        · exact mul_le_mul (mul_le_mul hA hp (norm_nonneg _) ((norm_nonneg _).trans hA))
            hq (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hA) ((norm_nonneg _).trans hp))
        · exact mul_le_mul hB ht (norm_nonneg _) ((norm_nonneg _).trans hB)
      · exact mul_le_mul (mul_le_mul hD hdp (norm_nonneg _) ((norm_nonneg _).trans hD))
          hdq (norm_nonneg _) (mul_nonneg ((norm_nonneg _).trans hD) ((norm_nonneg _).trans hdp))
    _ = _ := by ring

/-- The actual coefficient derivatives along the metric segment bound the three
classes of lower terms. Each first or second jet input is a componentwise bound
on the indicated genuine coordinate jet. -/
theorem norm_metricEulerJetLowerRemainder_le {ι : Type*} [Fintype ι] (S : ι → Mat)
    (g h : Mat) (p dp : ActionSlot ι → ℝ) (q : Fin 4 → ActionSlot ι → ℝ) (i : ι)
    (hseg : ∀ u ∈ Icc (0 : ℝ) 1, (fieldSegment g h u).det ≠ 0)
    {P H Q M : ℝ} (hP : ∀ s, ‖p s‖ ≤ P) (hH : ∀ s, ‖dp s‖ ≤ H)
    (hQ : ∀ a t, ‖q a t‖ ≤ Q)
    (hC₃ : ∀ a t u, u ∈ Icc (0 : ℝ) 1 →
      ‖thirdFDeriv (metricActionCoefficient S (a, i) t) (fieldSegment g h u) h h h‖ ≤ M * ‖h‖^3)
    (hL₁ : ∀ s t u, u ∈ Icc (0 : ℝ) 1 →
      ‖fderiv ℝ (metricEulerLowerCoefficient S i s t) (fieldSegment g h u)‖ ≤ M)
    (hL₂ : ∀ s t u, u ∈ Icc (0 : ℝ) 1 →
      ‖secondFDeriv (metricEulerLowerCoefficient S i s t) (fieldSegment g h u)‖ ≤ M)
    (hL₃ : ∀ s t u, u ∈ Icc (0 : ℝ) 1 →
      ‖thirdFDeriv (metricEulerLowerCoefficient S i s t) (fieldSegment g h u) h h h‖ ≤ M * ‖h‖^3) :
    ‖metricEulerJetLowerRemainder S g h p dp q i‖ ≤
      ((Fintype.card (ActionSlot ι) : ℝ)^2) *
        (M * ‖h‖^3 * P^2 + 2 * (M * ‖h‖^2) * P * H + M * ‖h‖ * H^2) +
        (4 * (Fintype.card (ActionSlot ι) : ℝ)) * (M * ‖h‖^3 * Q) := by
  have hq (a t) : ‖quadraticTaylorRemainder (metricActionCoefficient S (a, i) t) g h * q a t‖ ≤
      M * ‖h‖^3 * Q := by
    have hC := norm_quadraticTaylorRemainder_le (metricActionCoefficient S (a, i) t)
      isOpen_nonsingularMetricDomain (contDiffOn_metricActionCoefficient S (a, i) t) g h hseg (hC₃ a t)
    rw [norm_mul]
    exact mul_le_mul hC (hQ a t) (norm_nonneg _) ((norm_nonneg _).trans hC)
  have hp (s t) :
      let F := metricEulerLowerCoefficient S i s t
      ‖quadraticTaylorRemainder F g h * p s * p t +
        linearTaylorRemainder F g h * (dp s * p t + p s * dp t) +
        (F (g + h) - F g) * dp s * dp t‖ ≤
      M * ‖h‖^3 * P^2 + 2 * (M * ‖h‖^2) * P * H + M * ‖h‖ * H^2 := by
    let F := metricEulerLowerCoefficient S i s t
    have hF := contDiffOn_metricEulerLowerCoefficient S i s t
    exact norm_quadratic_first_jet_sum_le _ _ _ _ _ _ _
      (norm_quadraticTaylorRemainder_le F isOpen_nonsingularMetricDomain hF g h hseg (hL₃ s t))
      (norm_linearTaylorRemainder_le F isOpen_nonsingularMetricDomain hF g h hseg (hL₂ s t))
      (norm_sub_le_of_first_field_bound F isOpen_nonsingularMetricDomain hF g h hseg (hL₁ s t))
      (hP s) (hP t) (hH s) (hH t)
  have hqp := norm_double_sum_le _ hq
  have hpp := norm_double_sum_le _ hp
  unfold metricEulerJetLowerRemainder
  exact (norm_sub_le _ _).trans (add_le_add
    (by simpa only [pow_two] using hpp) (by simpa using hqp))

end Burnett.V03
