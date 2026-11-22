import Burnett.Analysis.GaugeProjection.GaugeProjectionSymbol
import Burnett.Analysis.AngularCaps.ActualEnlargedCapJets

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 350000

noncomputable section

namespace Burnett.P01

open Set Filter Metric
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.ProjectiveNullCaps (weighted_iteratedFDeriv_le_of_unitSphere)
open scoped ContDiff Topology

private theorem gaugeProjectionSymbol_scale_any (a b c d : Fin 4)
    (t : ℝ) (ht : t ≠ 0) (ξ : E) :
    gaugeProjectionSymbol a b c d (t • ξ) = gaugeProjectionSymbol a b c d ξ := by
  rcases lt_or_gt_of_ne ht with h | h
  · rw [show t • ξ = -((-t) • ξ) by simp, gaugeProjectionSymbol_even]
    exact gaugeProjectionSymbol_scale a b c d (-t) (neg_pos.mpr h) ξ
  · exact gaugeProjectionSymbol_scale a b c d t h ξ

private theorem smoothOrder_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ :=
  WithTop.coe_le_coe.mpr le_top

private theorem gaugeProjectionSymbol_iterated_bound_on_sphere (a b c d : Fin 4) (n : ℕ) :
    ∃ C : ℝ, ∀ ξ : E, ‖ξ‖ = 1 →
      ‖iteratedFDeriv ℝ n (gaugeProjectionSymbol a b c d) ξ‖ ≤ C := by
  let U : Set E := {ξ | ξ ≠ 0}
  have hU : IsOpen U := isOpen_ne
  have hSmooth := gaugeProjectionSymbol_contDiffOn a b c d
  have hContIn := hSmooth.continuousOn_iteratedFDerivWithin (smoothOrder_le_infty n) hU.uniqueDiffOn
  have hCont : ContinuousOn (iteratedFDeriv ℝ n (gaugeProjectionSymbol a b c d)) U :=
    hContIn.congr fun ξ hξ => (iteratedFDerivWithin_of_isOpen n hU hξ).symm
  have hSub : sphere (0 : E) 1 ⊆ U := by
    intro ξ hξ hz
    simpa [hz] using mem_sphere_zero_iff_norm.mp hξ
  obtain ⟨C,hC⟩ := (isCompact_sphere (0 : E) 1).exists_bound_of_continuousOn (hCont.mono hSub)
  exact ⟨C, fun ξ hξ => hC ξ (mem_sphere_zero_iff_norm.mpr hξ)⟩

/-- The actual smooth regularized symbol has bounded derivatives of every
order, so it acts on Schwartz tests and on their tempered dual. -/
theorem regularizedGaugeProjectionSymbol_hasTemperateGrowth (a b c d : Fin 4) :
    Function.HasTemperateGrowth (regularizedGaugeProjectionSymbol a b c d) := by
  refine ⟨regularizedGaugeProjectionSymbol_contDiff a b c d, fun n => ?_⟩
  obtain ⟨C1,hC1⟩ := gaugeProjectionSymbol_iterated_bound_on_sphere a b c d n
  have hCont := (regularizedGaugeProjectionSymbol_contDiff a b c d).continuous_iteratedFDeriv
    (smoothOrder_le_infty n)
  obtain ⟨C0,hC0⟩ := (isCompact_closedBall (0 : E) 3).exists_bound_of_continuousOn hCont.continuousOn
  refine ⟨0, max C0 C1, fun ξ => ?_⟩
  simp only [pow_zero, mul_one]
  by_cases hξ : ‖ξ‖ ≤ 3
  · exact (hC0 ξ (mem_closedBall_zero_iff.mpr hξ)).trans (le_max_left _ _)
  · have hNear : ∀ᶠ y in 𝓝 ξ, (2 : ℝ) < ‖y‖ :=
      (continuous_norm.tendsto ξ).eventually (Ioi_mem_nhds (lt_trans (by norm_num) (lt_of_not_ge hξ)))
    have hEq : regularizedGaugeProjectionSymbol a b c d =ᶠ[𝓝 ξ] gaugeProjectionSymbol a b c d :=
      hNear.mono fun y hy => regularizedGaugeProjectionSymbol_high a b c d hy.le
    rw [(hEq.iteratedFDeriv ℝ n).eq_of_nhds]
    have hξ0 : ξ ≠ 0 := by intro h; simp [h] at hξ
    have hWeighted := weighted_iteratedFDeriv_le_of_unitSphere
      (gaugeProjectionSymbol_contDiffOn a b c d) (gaugeProjectionSymbol_scale_any a b c d) hC1 hξ0
    have h1 : 1 ≤ ‖ξ‖ := by linarith only [lt_of_not_ge hξ]
    calc
      _ = 1 * ‖iteratedFDeriv ℝ n (gaugeProjectionSymbol a b c d) ξ‖ := (one_mul _).symm
      _ ≤ ‖ξ‖ ^ n * ‖iteratedFDeriv ℝ n (gaugeProjectionSymbol a b c d) ξ‖ :=
        mul_le_mul_of_nonneg_right (one_le_pow₀ h1) (norm_nonneg _)
      _ ≤ C1 := hWeighted
      _ ≤ _ := le_max_right _ _

end Burnett.P01
