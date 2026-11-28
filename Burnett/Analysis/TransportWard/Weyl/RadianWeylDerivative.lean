import Burnett.Analysis.TransportWard.Weyl.FrozenHessianCanonicalBracket
import Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

/-! The same real Weyl symbol differentiated in the two actual frequency
coordinates, with the conversion recovered from the chain rule. -/

set_option autoImplicit false
set_option maxHeartbeats 6400000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03

open Function Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.RotatingNullMoments.CanonicalHamilton (momentumPartial momentumBasis)
open scoped ContDiff

/-- Differentiating the exact normalized real Weyl test in cycles inserts
one factor (2π) relative to the canonical covector derivative. -/
theorem normalizedRealWeylSymbol_frequencyCoordinate (β : E → E → ℝ)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (k : Fin 4) (x ξ : E) :
    fderiv ℝ ((normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) x) ξ (coordinateDirection k) =
      (tau : ℂ) *
        (momentumPartial k (fun y p => β y (WithLp.toLp 2 p)) x (physicalRadianCovector ξ) : ℂ) := by
  let Q : E ≃L[ℝ] Covector := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)
  let L : E →L[ℝ] Covector := tau • Q.toContinuousLinearMap
  let b (p : Covector) := β x (Q.symm p)
  have hB : DifferentiableAt ℝ b (L ξ) := by
    change DifferentiableAt ℝ (uncurry β ∘ fun p : Covector => (x,Q.symm p)) (L ξ)
    exact (hβ.comp (contDiff_const.prodMk Q.symm.contDiff)).differentiable (by simp) _
  have hD : HasFDerivAt (Complex.ofRealCLM ∘ (b ∘ L))
      (Complex.ofRealCLM.comp ((fderiv ℝ b (L ξ)).comp L)) ξ :=
    Complex.ofRealCLM.hasFDerivAt.comp ξ (hB.hasFDerivAt.comp ξ L.hasFDerivAt)
  have he : L (coordinateDirection k) = tau • momentumBasis k := by
    funext j
    change tau * (EuclideanSpace.single k (1 : ℝ)) j = tau * momentumBasis k j
    simp only [EuclideanSpace.single_apply, momentumBasis, Pi.single_apply]
  have hEq : ((normalizedWeylSymbol (fun y ζ => (β y ζ : ℂ))) x) =
      Complex.ofRealCLM ∘ (b ∘ L) := by
    funext ζ
    change (β x (tau • ζ) : ℂ) = (β x (Q.symm (tau • Q ζ)) : ℂ)
    rw [map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rw [hEq, hD.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, he, map_smul]
  simp only [Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
  rfl

end Burnett.V03
