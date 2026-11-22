import Burnett.Analysis.GaugeProjection.GaugeProjectionTemperate

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open Filter Metric
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.ProjectiveNullCaps (weighted_iteratedFDeriv_le_of_unitSphere)
open scoped ContDiff Topology

open private gaugeProjectionSymbol_scale_any gaugeProjectionSymbol_iterated_bound_on_sphere
  smoothOrder_le_infty from Burnett.Analysis.GaugeProjection.GaugeProjectionTemperate

/-- Each actual regularized component of the four-dimensional projection
has the full weighted order-zero bounds. -/
theorem regularizedGaugeProjectionSymbol_orderZero_weighted (a b c d : Fin 4) :
    ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : E,
      (max 1 ‖ξ‖) ^ n * ‖iteratedFDeriv ℝ n (regularizedGaugeProjectionSymbol a b c d) ξ‖ ≤ C := by
  intro n
  obtain ⟨C₁, hC₁⟩ := gaugeProjectionSymbol_iterated_bound_on_sphere a b c d n
  have hCont := (regularizedGaugeProjectionSymbol_contDiff a b c d).continuous_iteratedFDeriv
    (smoothOrder_le_infty n)
  obtain ⟨C₀, hC₀⟩ := (isCompact_closedBall (0 : E) 3).exists_bound_of_continuousOn hCont.continuousOn
  refine ⟨max 0 (max ((3 : ℝ)^n * C₀) C₁), le_max_left _ _, ?_⟩
  intro ξ
  by_cases hξ : ‖ξ‖ ≤ 3
  · have hMax : max (1 : ℝ) ‖ξ‖ ≤ 3 := max_le (by norm_num) hξ
    calc
      _ ≤ (3 : ℝ)^n * C₀ := mul_le_mul
        (pow_le_pow_left₀ (le_trans zero_le_one (le_max_left _ _)) hMax n)
        (hC₀ ξ (mem_closedBall_zero_iff.mpr hξ)) (norm_nonneg _) (by positivity)
      _ ≤ _ := (le_max_left _ _).trans (le_max_right _ _)
  · have hNear : ∀ᶠ y in 𝓝 ξ, (2 : ℝ) < ‖y‖ :=
      (continuous_norm.tendsto ξ).eventually (Ioi_mem_nhds (lt_trans (by norm_num) (lt_of_not_ge hξ)))
    have hEq : regularizedGaugeProjectionSymbol a b c d =ᶠ[𝓝 ξ] gaugeProjectionSymbol a b c d :=
      hNear.mono fun y hy => regularizedGaugeProjectionSymbol_high a b c d hy.le
    have hξ₀ : ξ ≠ 0 := by
      intro h
      simp [h] at hξ
    have hOne : 1 ≤ ‖ξ‖ := by linarith only [lt_of_not_ge hξ]
    rw [max_eq_right hOne, (hEq.iteratedFDeriv ℝ n).eq_of_nhds]
    exact (weighted_iteratedFDeriv_le_of_unitSphere (gaugeProjectionSymbol_contDiffOn a b c d)
      (gaugeProjectionSymbol_scale_any a b c d) hC₁ hξ₀).trans
        ((le_max_right _ _).trans (le_max_right _ _))

end Burnett.P01
