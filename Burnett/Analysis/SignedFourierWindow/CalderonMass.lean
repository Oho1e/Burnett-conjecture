import Burnett.Analysis.SignedFourierWindow.CalderonGood

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set Function
open scoped ENNReal

/-- The total L¹ mass of the countable mean-zero blocks is bounded by twice
the mass of the input on their union. -/
theorem bad_blocks_total {ι : Type*} [Countable ι] (f : Space → ℂ) (hf : Integrable f)
    (Q : ι → Set Space) (hm : ∀ i, MeasurableSet (Q i)) (hd : Pairwise (Disjoint on Q))
    (hfin : ∀ i, volume (Q i) < ⊤) :
    (∑' i, ∫⁻ x, ‖badBlock f (Q i) x‖ₑ) ≤ 2*∫⁻ x in ⋃ i,Q i, ‖f x‖ₑ := by
  have each (i : ι) : (∫⁻ x, ‖badBlock f (Q i) x‖ₑ) ≤ 2*∫⁻ x in Q i, ‖f x‖ₑ := by
    obtain ⟨hi,_,h⟩ := bad_block_integral f hf (Q i) (hm i) (hfin i)
    have h' := ENNReal.ofReal_le_ofReal h
    rw [ofReal_integral_norm_eq_lintegral_enorm hi, ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ofReal_integral_norm_eq_lintegral_enorm hf.integrableOn] at h'
    simpa using h'
  calc
    _ ≤ ∑' i, 2*∫⁻ x in Q i, ‖f x‖ₑ := ENNReal.tsum_le_tsum each
    _ = _ := by rw [ENNReal.tsum_mul_left, lintegral_iUnion hm hd]

end Burnett.Analysis.SignedFourierWindow
