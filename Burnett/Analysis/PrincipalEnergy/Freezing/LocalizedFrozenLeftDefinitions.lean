import Burnett.Analysis.PrincipalEnergy.Freezing.RadianLeftFullSymbol

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Burnett.A02.FrequencySplit

/-- The paper's localized principal symbol, before multiplication by -i. -/
def localizedFrozenPrincipalSymbol (a : E → E → ℝ) (c : E) (θ : SchwartzMap E ℂ)
    (x ξ : E) : ℂ :=
  (θ x)^2 * ((a x ξ : ℂ) - (a c ξ : ℂ))

/-- This is the actual left commutator in the comparison, with the
common output cutoff and the difference from the frozen multiplier. -/
def localizedFrozenLeftCommutator (a : E → E → ℝ) (c : E) (θ : SchwartzMap E ℂ)
    (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  θ x * (radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) (energyProduct θ u) x -
    θ x * radianLeftQuantization (fun y ξ => (a y ξ : ℂ)) u x - radianCommutator (a c) θ u x)

end Burnett.A03
