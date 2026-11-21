import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianCommutator

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Finset Burnett.RicciSymbol
open scoped ContDiff FourierTransform

/-- The paper's three symbols at the radian frequencies of the same two
Schwartz inputs, with the outside and input angular coefficients in their
respective slots. -/
theorem radian_commutator_symbol_split (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) (η ξ : E) :
    b (tau • (η+ξ)) - b (tau • ξ) =
      (∑ j, (tau * η j) * lowSymbol b j η ξ) +
      (∑ j, angularComponent b j (η+ξ) * productSymbol j η ξ * ‖tau • η‖) -
      ∑ j, inputSymbol j η ξ * ‖tau • η‖ * angularComponent b j ξ := by
  have tauPos : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have scaled := commutator_symbol_eq b hb (homogeneous_value_zero hom) (tau • η) (tau • ξ)
  have low (j : Index) := lowSymbol_scale hb hom j tau tauPos η ξ
  have high (j : Index) := highSymbols_scale j tau tauPos η ξ
  have component (j : Index) (z : E) := angularComponent_scale hom j tau tauPos z
  have coordinate (j : Index) : (tau • η) j = tau * η j := rfl
  simpa only [← smul_add, low, component, fun j => (high j).1, fun j => (high j).2, coordinate]
    using scaled

end Burnett.A02.FrequencySplit
