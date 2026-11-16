import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Filter
open scoped Topology BigOperators

variable {α ι : Type*} [MeasurableSpace α] [Fintype ι]
  {μ : Measure α}

set_option maxHeartbeats 800000 in
/-- Finite sums with uniformly bounded coefficients preserve vanishing
whole-space squared energy. No cancellation between different modes is
assumed. -/
theorem finite_energy_tendsto_zero
    {G : ℕ → ι → α → ℂ} {a : ℕ → ι → ℂ}
    (hGm : ∀ n i, AEStronglyMeasurable (G n i) μ)
    (hGi : ∀ n i, Integrable (fun x => ‖G n i x‖^2) μ)
    (ha : ∀ n i, ‖a n i‖ ≤ 1)
    (hGt : ∀ i, Tendsto (fun n => ∫ x, ‖G n i x‖^2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, ‖∑ i, a n i * G n i x‖^2 ∂μ) atTop (𝓝 0) := by
  classical
  have hb (n : ℕ) (x : α) :
      ‖∑ i, a n i * G n i x‖^2 ≤ (Fintype.card ι : ℝ) * ∑ i, ‖G n i x‖^2 := by
    have hn : ‖∑ i, a n i * G n i x‖ ≤ ∑ i, ‖G n i x‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (ha n i) (norm_nonneg _)).trans_eq (one_mul _)
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : ι => (1 : ℝ)) (fun i => ‖G n i x‖)
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      mul_one] at hcs
    exact (sq_le_sq₀ (norm_nonneg _) (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) |>.mpr hn).trans hcs
  have hsumint (n : ℕ) : Integrable (fun x => (Fintype.card ι : ℝ) *
      ∑ i, ‖G n i x‖^2) μ :=
    (integrable_finset_sum _ (fun i _ => hGi n i)).const_mul _
  have hHi (n : ℕ) : Integrable (fun x => ‖∑ i, a n i * G n i x‖^2) μ := by
    have hHm : AEStronglyMeasurable (fun x => ∑ i, a n i * G n i x) μ := by
      exact Finset.aestronglyMeasurable_fun_sum Finset.univ
        (fun i _ => (hGm n i).const_mul (a n i))
    apply (hsumint n).mono'
    · exact hHm.norm.pow 2
    · filter_upwards with x
      simpa only [Real.norm_of_nonneg (sq_nonneg _)] using hb n x
  apply squeeze_zero
  · intro n
    exact integral_nonneg (fun _ => sq_nonneg _)
  · intro n
    exact integral_mono (hHi n) (hsumint n) (hb n)
  · have ht := (tendsto_finset_sum Finset.univ (fun i _ => hGt i)).const_mul
      (Fintype.card ι : ℝ)
    simpa only [Finset.sum_const_zero, mul_zero, integral_const_mul,
      integral_finset_sum _ (fun i _ => hGi _ i)] using ht

end Burnett.Fourier
