import Burnett.Analysis.TransportWard.Weyl.RadianWeylDerivative
import Burnett.Analysis.TransportWard.Weyl.CoefficientCommutatorTaylor

/-! The exact cancellation of the radian conversion in the leading
symbol of the coefficient commutator. -/

set_option autoImplicit false
set_option maxHeartbeats 3100000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.V03

open Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.RotatingNullMoments.CanonicalHamilton (momentumPartial)
open scoped BigOperators ContDiff

theorem coefficientCommutatorLeading_normalizedWeyl (β : E → E → ℝ)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (c : SchwartzMap E ℂ) (x ξ : E) :
    coefficientCommutatorLeading (normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) c x ξ =
      ∑ k : Fin 4, (frozenSchwartzCoordinatePartial k c) x *
        (momentumPartial k (fun y p => β y (WithLp.toLp 2 p)) x (physicalRadianCovector ξ) : ℂ) := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have ht' : (tau : ℂ) ≠ 0 := by exact_mod_cast ht.ne'
  simp only [coefficientCommutatorLeading, normalizedRealWeylSymbol_frequencyCoordinate β hβ]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  let D := (frozenSchwartzCoordinatePartial k c) x
  let p := (momentumPartial k (fun y q => β y (WithLp.toLp 2 q)) x (physicalRadianCovector ξ) : ℂ)
  change (tau : ℂ)⁻¹ * D * ((tau : ℂ) * p) = D * p
  calc
    _ = ((tau : ℂ)⁻¹ * (tau : ℂ)) * (D * p) := by ring
    _ = _ := by rw [inv_mul_cancel₀ ht', one_mul]

end Burnett.V03
