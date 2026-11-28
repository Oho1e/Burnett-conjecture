import Burnett.Analysis.TransportWard.Weyl.ActualDensityBaseSymbol
import Burnett.Analysis.TransportWard.Weyl.CanonicalBracketDecomposition

set_option autoImplicit false
set_option maxHeartbeats 340000
set_option maxRecDepth 1600

noncomputable section

namespace Burnett.V03.Palatini

open Function Filter Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open scoped BigOperators ContDiff Topology

local notation "J" => Fin 4 × Fin 4

/-- The exact frozen and variable principal terms of the same density Weyl
commutator sum to the canonical bracket at the original radian phase. -/
theorem variableDensityWeylLeading_eq_canonicalBracket {ι : Type*}
    (S : ι → Mat) (G : E → Mat) (c : ι → ι → J → SchwartzMap E ℂ)
    (β : E → E → ℝ) (hβ : ContDiff ℝ ∞ (uncurry β)) (i j : ι) (x ξ : E)
    (hC : ∀ d : J, DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x)
    (hc : ∀ d : J, (fun y => c i j d y) =ᶠ[𝓝 x]
      fun y => (metricActionCoefficient S (d.1,i) (d.2,j) (G y) : ℂ)) :
    let b := normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))
    let p := physicalRadianCovector ξ
    (frozenHessianTransportMatrix S (G x) b i j x ξ +
        ∑ d : J, -((p d.1 : ℂ) * (p d.2 : ℂ)) *
          coefficientCommutatorLeading b (c i j d) x ξ) =
      (canonicalBracket (fun y q => frozenDensityPrincipalPhase S (G y) q i j)
        (fun y q => β y (WithLp.toLp 2 q)) x p : ℂ) := by
  intro b p
  have hu := frozenHessianTransportMatrix_eq_frozen_canonicalBracket S (G x) β hβ i j x ξ
  have hv := actualDensityVariableLeading_eq_negativeBaseSymbol S G c β hβ i j x ξ hC hc
  exact add_frozenCanonicalBracket_negativeBase
    (fun y q => frozenDensityPrincipalPhase S (G y) q i j)
    (fun y q => β y (WithLp.toLp 2 q)) x p hu hv

end Burnett.V03.Palatini
