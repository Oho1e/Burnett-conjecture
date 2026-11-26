import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneWeightedJets
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.SmoothSymbolJetLimits
import Mathlib.Topology.Sequences

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace Burnett.A06

open Set Filter Metric
open Burnett.A02.FrequencySplit (Joint)
open scoped ContDiff Topology

private def recoverJet (u : WeightedOrderOneJetSpace) (n : ℕ) (x : Joint) :
    Joint[×n]→L[ℝ] ℂ :=
  (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x)⁻¹ • u n x

private theorem weight_pos (n : ℕ) (x : Joint) :
    0 < symbolFrequencyWeight x ^ n / symbolFrequencyWeight x :=
  div_pos (pow_pos (symbolFrequencyWeight_pos x) _) (symbolFrequencyWeight_pos x)

private theorem reconstruct_weighted_jet (u : WeightedOrderOneJetSpace) (n : ℕ) (x : Joint) :
    (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x) • recoverJet u n x = u n x :=
  smul_inv_smul₀ (weight_pos n x).ne' _

private theorem recover_weighted_derivative (b : OrderOneSymbol ℂ) (n : ℕ) (x : Joint) :
    recoverJet (orderOneWeightedJets b) n x = iteratedFDeriv ℝ n (b : Joint → ℂ) x := by
  rw [recoverJet,orderOneWeightedJets_apply,inv_smul_smul₀ (weight_pos n x).ne']

private theorem weight_inverse_le_on_ball (n : ℕ) (R : ℝ) {x : Joint} (hx : x ∈ ball 0 R) :
    (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x)⁻¹ ≤ 1+2*|R| := by
  have hX := (mem_ball_zero_iff.mp hx).le.trans (le_abs_self R)
  have hW : 1 ≤ symbolFrequencyWeight x := by
    unfold symbolFrequencyWeight
    linarith only [norm_nonneg x.1,norm_nonneg x.2]
  have first : ‖x.1‖ ≤ |R| := (le_max_left ‖x.1‖ ‖x.2‖).trans hX
  have second : ‖x.2‖ ≤ |R| := (le_max_right ‖x.1‖ ‖x.2‖).trans hX
  calc
    _ = symbolFrequencyWeight x / symbolFrequencyWeight x ^ n := inv_div _ _
    _ ≤ symbolFrequencyWeight x :=
      (div_le_self (symbolFrequencyWeight_pos x).le (one_le_pow₀ hW))
    _ ≤ _ := by unfold symbolFrequencyWeight; linarith only [first,second]

/-- A convergent sequence of actual weighted symbols keeps compatible
derivatives and the original weighted bounds. The range of the full jet
map is closed in the countable Banach product. -/
theorem isClosed_range_orderOneWeightedJets : IsClosed (range orderOneWeightedJets) := by
  classical
  refine isClosed_of_closure_subset ?_
  intro u hu
  obtain ⟨v, hv, hLim⟩ := mem_closure_iff_seq_limit.mp hu
  choose b hb using hv
  have coord (n : ℕ) :
      Tendsto (fun k => orderOneWeightedJets (b k) n) atTop (𝓝 (u n)) := by
    have hP := ((continuous_apply n).tendsto u).comp hLim
    simpa only [Function.comp_apply, hb] using hP
  have balls (n : ℕ) (R : ℝ) : TendstoUniformlyOn
      (fun k => iteratedFDeriv ℝ n (b k : Joint → ℂ)) (recoverJet u n) atTop (ball 0 R) := by
    refine Metric.tendstoUniformlyOn_iff.mpr (fun ε hε => ?_)
    let C := 1+2*|R|
    have hC : 0 < C := by dsimp [C]; positivity
    filter_upwards [Metric.tendsto_nhds.mp (coord n) (ε/C) (div_pos hε hC)] with k hk
    intro x hx
    have hz : 0 < (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x)⁻¹ := inv_pos.mpr (weight_pos n x)
    have hPoint : ‖orderOneWeightedJets (b k) n x - u n x‖ < ε / C := by
      rw [← dist_eq_norm]
      exact (BoundedContinuousFunction.dist_coe_le_dist x).trans_lt hk
    rw [← recover_weighted_derivative (b k) n x,dist_eq_norm,recoverJet,recoverJet,← smul_sub,
      norm_smul,Real.norm_of_nonneg hz.le,norm_sub_rev]
    refine (mul_le_mul_of_nonneg_right (weight_inverse_le_on_ball n R hx) (norm_nonneg _)).trans_lt ?_
    exact (mul_lt_mul_of_pos_left hPoint hC).trans_eq (by field_simp [hC.ne'])
  obtain ⟨f, hf, jets⟩ := exists_smooth_symbol_of_uniform_jet_limits (fun k => (b k : Joint → ℂ))
    (fun k => (b k).contDiff) (recoverJet u) balls
  have hEq (n : ℕ) (x : Joint) :
      (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x) • iteratedFDeriv ℝ n f x = u n x := by
    rw [← jets n]
    exact reconstruct_weighted_jet u n x
  have hBound (n : ℕ) : BddAbove (range (orderOneWeightedJet n f)) := by
    refine ⟨‖u n‖,?_⟩
    rintro a ⟨x,rfl⟩
    have he : ‖u n x‖ = orderOneWeightedJet n f x := by
      rw [← hEq n x,norm_smul,Real.norm_of_nonneg (weight_pos n x).le,orderOneWeightedJet,mul_comm]
    rw [← he]
    exact (u n).norm_coe_le_norm x
  let symbol : OrderOneSymbol ℂ := ⟨f, mem_orderOneSymbolSubmodule_iff.mpr ⟨hf, hBound⟩⟩
  refine ⟨symbol, ?_⟩
  funext n
  apply BoundedContinuousFunction.ext
  intro x
  rw [orderOneWeightedJets_apply]
  exact hEq n x

end Burnett.A06
