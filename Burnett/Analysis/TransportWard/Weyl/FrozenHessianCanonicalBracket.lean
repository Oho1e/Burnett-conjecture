import Burnett.Analysis.TransportWard.Weyl.FrozenScalarCommutator
import Burnett.Analysis.TransportWard.Weyl.FrozenDensityPrincipalPhase

/-! The exact sign and radian normalization of the frozen Hessian's
principal Poisson bracket with the same scalar symbol. -/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxRecDepth 4700

noncomputable section

namespace Burnett.V03.Palatini

open Function Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol (Mat)
open Burnett.Analysis.FirstOrderDyadic (baseDirectionSymbol)
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.Bianchi.RayIdentification (canonicalBracket)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial)
open scoped BigOperators ComplexConjugate ContDiff

local notation "J" => Fin 4 × Fin 4

/-- The order-two part of the frozen commutator symbol before the scalar
test is written using the radian covector coordinates. -/
def frozenHessianTransportMatrix {ι : Type*} (S : ι → Mat) (G : Mat) (a : E → E → ℂ)
    (i j : ι) (x ξ : E) : ℂ :=
  ∑ d : J, (metricActionCoefficient S (d.1,i) (d.2,j) G : ℂ) *
    ((physicalRadianCovector ξ d.2 : ℂ) * baseDirectionSymbol a (coordinateDirection d.1) x ξ +
      (physicalRadianCovector ξ d.1 : ℂ) * baseDirectionSymbol a (coordinateDirection d.2) x ξ)

private theorem baseDirectionSymbol_normalizedReal (β : E → E → ℝ)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (x ξ : E) (a : Fin 4) :
    baseDirectionSymbol (normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) (coordinateDirection a) x ξ =
      (basePartial a (fun y p => β y (WithLp.toLp 2 p)) x (physicalRadianCovector ξ) : ℂ) := by
  have hb : DifferentiableAt ℝ (fun y => β y (tau • ξ)) x :=
    (hβ.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) x
  have hd := (Complex.ofRealCLM.hasFDerivAt.comp x hb.hasFDerivAt).fderiv
  change (fderiv ℝ (Complex.ofRealCLM ∘ (fun y => β y (tau • ξ))) x) (coordinateDirection a) = _
  rw [hd, ContinuousLinearMap.comp_apply]
  rfl

/-- The positive frozen leading symbol from the exact commutator is the
paper's canonical `{A,β}`, evaluated at the same actual radian covector. -/
theorem frozenHessianTransportMatrix_eq_frozen_canonicalBracket {ι : Type*} (S : ι → Mat) (G : Mat)
    (β : E → E → ℝ) (hβ : ContDiff ℝ ∞ (uncurry β)) (i j : ι) (x ξ : E) :
    frozenHessianTransportMatrix S G (normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) i j x ξ =
      (canonicalBracket (fun _ : E => fun q => frozenDensityPrincipalPhase S G q i j)
        (fun y q => β y (WithLp.toLp 2 q)) x (physicalRadianCovector ξ) : ℂ) := by
  rw [frozenDensityPrincipalPhase_bracket]
  simp only [frozenHessianTransportMatrix, Complex.ofReal_sum, Complex.ofReal_mul,
    Complex.ofReal_add, baseDirectionSymbol_normalizedReal β hβ]

end Burnett.V03.Palatini
