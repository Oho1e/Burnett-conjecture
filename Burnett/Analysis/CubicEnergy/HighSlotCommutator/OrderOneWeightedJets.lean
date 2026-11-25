import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneSymbolSpace
import Mathlib.Topology.ContinuousMap.Bounded.Normed

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

namespace Burnett.A06

open Set Metric
open Burnett.A02.FrequencySplit (Joint)
open scoped ContDiff

abbrev WeightedOrderOneJetSpace := ∀ n : ℕ, BoundedContinuousFunction Joint (Joint[×n]→L[ℝ] ℂ)

private def orderOneJetWeight (n : ℕ) (x : Joint) : ℝ :=
  symbolFrequencyWeight x ^ n / symbolFrequencyWeight x

private theorem orderOneJetWeight_pos (n : ℕ) (x : Joint) : 0 < orderOneJetWeight n x :=
  div_pos (pow_pos (symbolFrequencyWeight_pos x) _) (symbolFrequencyWeight_pos x)

private theorem orderOneJetWeight_continuous (n : ℕ) : Continuous (orderOneJetWeight n) := by
  have h : Continuous symbolFrequencyWeight := (continuous_const.add continuous_fst.norm).add continuous_snd.norm
  exact (h.pow n).div h (fun x => (symbolFrequencyWeight_pos x).ne')

private theorem finiteOrder_le_infty (n : ℕ) : (n : WithTop ℕ∞) ≤ ∞ := by
  change ((n : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
  exact WithTop.coe_le_coe.mpr le_top

private def orderOneBoundedJet (b : OrderOneSymbol ℂ) (n : ℕ) : BoundedContinuousFunction Joint (Joint[×n]→L[ℝ] ℂ) := by
  let F (x : Joint) := orderOneJetWeight n x • iteratedFDeriv ℝ n (b : Joint → ℂ) x
  have hF : Continuous F :=
    (orderOneJetWeight_continuous n).smul (b.contDiff.continuous_iteratedFDeriv (finiteOrder_le_infty n))
  refine BoundedContinuousFunction.ofNormedAddCommGroup F hF (orderOneWeightedSeminorm ℂ n b) ?_
  intro x
  rw [show ‖F x‖ = orderOneWeightedJet n (b : Joint → ℂ) x from by
    change ‖orderOneJetWeight n x • iteratedFDeriv ℝ n (b : Joint → ℂ) x‖ = _
    rw [norm_smul,Real.norm_of_nonneg (orderOneJetWeight_pos n x).le,orderOneWeightedJet,mul_comm]
    rfl]
  rw [orderOneWeightedSeminorm_apply]
  have bd := (mem_orderOneSymbolSubmodule_iff.mp b.property).2 n
  exact le_csSup bd (mem_range_self x)

/-- Real-linear embedding of the manuscript's symbols into the product
of bounded continuous weighted derivatives. -/
def orderOneWeightedJets : OrderOneSymbol ℂ →ₗ[ℝ] WeightedOrderOneJetSpace where
  toFun b := orderOneBoundedJet b
  map_add' b c := by
    funext n
    apply BoundedContinuousFunction.ext
    intro x
    have bs := (b.contDiff.of_le (finiteOrder_le_infty n)).contDiffAt (x := x)
    have cs := (c.contDiff.of_le (finiteOrder_le_infty n)).contDiffAt (x := x)
    change orderOneJetWeight n x • iteratedFDeriv ℝ n ((b : Joint → ℂ)+(c : Joint → ℂ)) x =
      orderOneJetWeight n x • iteratedFDeriv ℝ n (b : Joint → ℂ) x +
      orderOneJetWeight n x • iteratedFDeriv ℝ n (c : Joint → ℂ) x
    rw [iteratedFDeriv_add_apply bs cs,smul_add]
  map_smul' a b := by
    funext n
    apply BoundedContinuousFunction.ext
    intro x
    have bs := (b.contDiff.of_le (finiteOrder_le_infty n)).contDiffAt (x := x)
    change orderOneJetWeight n x • iteratedFDeriv ℝ n (a • (b : Joint → ℂ)) x =
      a • (orderOneJetWeight n x • iteratedFDeriv ℝ n (b : Joint → ℂ) x)
    rw [iteratedFDeriv_const_smul_apply bs,smul_smul,smul_smul,mul_comm]

theorem orderOneWeightedJets_apply (b : OrderOneSymbol ℂ) (n : ℕ) (x : Joint) :
    orderOneWeightedJets b n x =
      (symbolFrequencyWeight x ^ n / symbolFrequencyWeight x) • iteratedFDeriv ℝ n (b : Joint → ℂ) x :=
  rfl

theorem norm_orderOneWeightedJets_apply (b : OrderOneSymbol ℂ) (n : ℕ) :
    ‖orderOneWeightedJets b n‖ = orderOneWeightedSeminorm ℂ n b := by
  rw [BoundedContinuousFunction.norm_eq_iSup_norm,orderOneWeightedSeminorm_apply]
  change (⨆ x : Joint, ‖orderOneWeightedJets b n x‖) = ⨆ x : Joint, orderOneWeightedJet n (b : Joint → ℂ) x
  congr 1
  funext x
  have hp : 0 ≤ symbolFrequencyWeight x ^ n / symbolFrequencyWeight x := (orderOneJetWeight_pos n x).le
  rw [orderOneWeightedJets_apply,norm_smul, Real.norm_of_nonneg hp,orderOneWeightedJet,mul_comm]

theorem orderOneWeightedJets_injective : Function.Injective orderOneWeightedJets := by
  intro b c eq
  apply Subtype.ext
  funext x
  let m : Fin 0 → Joint := fun _ => 0
  have e := congrArg (fun A : WeightedOrderOneJetSpace => A 0 x m) eq
  change (orderOneWeightedJets b 0 x) m = (orderOneWeightedJets c 0 x) m at e
  simp only [orderOneWeightedJets_apply, ContinuousMultilinearMap.smul_apply, iteratedFDeriv_zero_apply] at e
  exact smul_right_injective ℂ (orderOneJetWeight_pos 0 x).ne' e

end Burnett.A06
