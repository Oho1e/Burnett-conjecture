import Burnett.Analysis.CubicEnergy.HighSlotCommutator.OrderOneSymbolSpace
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotSymbolLinearity

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit (E Joint)

/-- The zeroth order seminorm bounds the actual value of the order-one symbol
at each of the physical frequency pairs. -/
theorem OrderOneSymbol.norm_apply_le_weightedSeminorm_zero
    (b : OrderOneSymbol ℂ) (x : Joint) :
    ‖(b : Joint → ℂ) x‖ ≤ orderOneWeightedSeminorm ℂ 0 b * (1 + ‖x.1‖ + ‖x.2‖) := by
  have bounded := (mem_orderOneSymbolSubmodule_iff.mp b.property).2 0
  have h : orderOneWeightedJet 0 (b : Joint → ℂ) x ≤ orderOneWeightedSeminorm ℂ 0 b := by
    rw [orderOneWeightedSeminorm_apply]
    exact le_csSup bounded (Set.mem_range_self x)
  have hdiv : ‖(b : Joint → ℂ) x‖ / symbolFrequencyWeight x ≤
      orderOneWeightedSeminorm ℂ 0 b := by
    simpa only [orderOneWeightedJet, norm_iteratedFDeriv_zero, pow_zero, one_div,
      div_eq_mul_inv, one_mul] using h
  exact (div_le_iff₀ (symbolFrequencyWeight_pos x)).mp hdiv

theorem OrderOneSymbol.measurable_symbol (b : OrderOneSymbol ℂ) :
    Measurable (b : Joint → ℂ) :=
  b.contDiff.continuous.measurable

theorem realOrderOneSymbolSeminorm_zero_apply (b : OrderOneSymbol ℂ) :
    realOrderOneSymbolSeminorm ℂ 0 b = orderOneWeightedSeminorm ℂ 0 b := by
  simp [realOrderOneSymbolSeminorm, orderOneSymbolSeminorm]

/-- For fixed Schwartz fields and a real Lipschitz high-slot coefficient, the
actual trilinear test pairing defines a real linear functional of the symbol. -/
def radianHighCommutatorSymbolLinearMap
    (d : E → ℝ) (L : NNReal) (hd : LipschitzWith L d) (h0 : d 0 = 0)
    (f g h : SchwartzMap E ℂ) : OrderOneSymbol ℂ →ₗ[ℝ] ℂ where
  toFun b := radianHighCommutatorPair b d f g h
  map_add' b c := by
    change radianHighCommutatorPair ((b : Joint → ℂ) + (c : Joint → ℂ)) d f g h =
      radianHighCommutatorPair b d f g h + radianHighCommutatorPair c d f g h
    exact radianHighCommutatorPair_add_symbol b c b.measurable_symbol c.measurable_symbol _ _
      (apply_nonneg _ _) (apply_nonneg _ _) b.norm_apply_le_weightedSeminorm_zero
      c.norm_apply_le_weightedSeminorm_zero d L hd h0 f g h
  map_smul' a b := by
    change radianHighCommutatorPair (a • (b : Joint → ℂ)) d f g h =
      a • radianHighCommutatorPair b d f g h
    exact radianHighCommutatorPair_real_smul_symbol a _ _ _ _ _

@[simp] theorem radianHighCommutatorSymbolLinearMap_apply
    (d : E → ℝ) (L : NNReal) (hd : LipschitzWith L d) (h0 : d 0 = 0)
    (f g h : SchwartzMap E ℂ) (b : OrderOneSymbol ℂ) :
    radianHighCommutatorSymbolLinearMap d L hd h0 f g h b =
      radianHighCommutatorPair b d f g h := rfl

theorem exists_radianHighCommutatorSymbolLinearMap_bound (f g h : SchwartzMap E ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (d : E → ℝ) (L : NNReal) (hd : LipschitzWith L d) (h0 : d 0 = 0)
      (b : OrderOneSymbol ℂ), ‖radianHighCommutatorSymbolLinearMap d L hd h0 f g h b‖ ≤
        C * realOrderOneSymbolSeminorm ℂ 0 b * (L : ℝ) := by
  obtain ⟨C, C0, hC⟩ := exists_radianHighCommutatorPair_test_bound f g h
  refine ⟨C, C0, ?_⟩
  intro d L hd h0 b
  rw [radianHighCommutatorSymbolLinearMap_apply, realOrderOneSymbolSeminorm_zero_apply]
  exact (hC b b.measurable_symbol _ (apply_nonneg _ _) b.norm_apply_le_weightedSeminorm_zero
    d L hd h0).2.2

end Burnett.A06
