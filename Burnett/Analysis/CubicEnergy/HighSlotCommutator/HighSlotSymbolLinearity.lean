import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotFixedTest

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit (E Joint tau)

/-- Addition in the symbol on the same absolutely integrable Fourier pairing. -/
private theorem radianHighPair_add_symbol
    (b c : Joint → ℂ) (f u v : E → ℂ)
    (hb : Integrable (radianHighPairWeight b f u v))
    (hc : Integrable (radianHighPairWeight c f u v)) :
    radianHighPair (b + c) f u v = radianHighPair b f u v + radianHighPair c f u v := by
  have eq : radianHighPairWeight (b + c) f u v =
      fun p => radianHighPairWeight b f u v p + radianHighPairWeight c f u v p := by
    funext p
    simp only [radianHighPairWeight, Pi.add_apply, add_mul]
  unfold radianHighPair
  rw [eq, integral_add hb hc, smul_add]

private theorem radianHighPair_real_smul_symbol
    (a : ℝ) (b : Joint → ℂ) (f u v : E → ℂ) :
    radianHighPair (a • b) f u v = a • radianHighPair b f u v := by
  have eq : radianHighPairWeight (a • b) f u v =
      fun p => a • radianHighPairWeight b f u v p := by
    funext p
    simp only [radianHighPairWeight, Pi.smul_apply, Complex.real_smul, mul_assoc]
  unfold radianHighPair
  rw [eq, integral_smul]
  exact smul_comm _ _ _

/-- The actual high-slot commutator pairing is additive in a measurable
symbol with a pointwise order-one growth bound. -/
theorem radianHighCommutatorPair_add_symbol
    (b c : Joint → ℂ) (hb : Measurable b) (hc : Measurable c)
    (B C : ℝ) (B0 : 0 ≤ B) (C0 : 0 ≤ C)
    (hB : ∀ p : Joint, ‖b p‖ ≤ B * (1 + ‖p.1‖ + ‖p.2‖))
    (hC : ∀ p : Joint, ‖c p‖ ≤ C * (1 + ‖p.1‖ + ‖p.2‖))
    (d : E → ℝ) (L : NNReal) (hd : LipschitzWith L d) (h0 : d 0 = 0)
    (f g h : SchwartzMap E ℂ) :
    radianHighCommutatorPair (b + c) d f g h =
      radianHighCommutatorPair b d f g h + radianHighCommutatorPair c d f g h := by
  obtain ⟨_, _, bound⟩ := exists_radianHighCommutatorPair_test_bound f g h
  obtain ⟨ib1, ib2, _⟩ := bound b hb B B0 hB d L hd h0
  obtain ⟨ic1, ic2, _⟩ := bound c hc C C0 hC d L hd h0
  unfold radianHighCommutatorPair
  rw [radianHighPair_add_symbol _ _ _ _ _ ib1 ic1, radianHighPair_add_symbol _ _ _ _ _ ib2 ic2]
  abel

/-- The same symbol scaling acts on both high-slot terms. -/
theorem radianHighCommutatorPair_real_smul_symbol
    (a : ℝ) (b : Joint → ℂ) (d : E → ℝ) (f g h : E → ℂ) :
    radianHighCommutatorPair (a • b) d f g h =
      a • radianHighCommutatorPair b d f g h := by
  unfold radianHighCommutatorPair
  rw [radianHighPair_real_smul_symbol, radianHighPair_real_smul_symbol, smul_sub]

end Burnett.A06
