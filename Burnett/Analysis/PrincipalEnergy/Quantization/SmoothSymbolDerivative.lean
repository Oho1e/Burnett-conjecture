import Burnett.Analysis.PrincipalEnergy.Quantization.ActualDerivative

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff

/-- Joint smoothness supplies the continuity of the actual base derivative at
fixed base point and direction, with no extra Fourier-domain condition. -/
theorem baseDirectionSymbol_continuous {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (Function.uncurry a)) (x e : E) :
    Continuous (baseDirectionSymbol a e x) := by
  let L := ContinuousLinearMap.inl ℝ E E
  have hDiff : Differentiable ℝ (Function.uncurry a) :=
    ha.differentiable (by simp)
  have hFormula (ξ : E) :
      baseDirectionSymbol a e x ξ = fderiv ℝ (Function.uncurry a) (x,ξ) (e,0) := by
    have hLine : HasFDerivAt (fun y => (y,ξ)) L x := by
      exact (L.hasFDerivAt.add_const (0,ξ)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => by simp [L])
    have hA := (hDiff (x,ξ)).hasFDerivAt.comp x hLine
    change fderiv ℝ ((Function.uncurry a) ∘ fun y => (y,ξ)) x e = _
    rw [hA.fderiv]
    rfl
  rw [show baseDirectionSymbol a e x = (fun ξ => fderiv ℝ (Function.uncurry a) (x,ξ) (e,0))
    from funext hFormula]
  exact ((ha.continuous_fderiv (by simp)).comp (continuous_const.prodMk continuous_id)).clm_apply
    continuous_const

/-- For a smooth actual symbol, the paper's spatial derivative commutator is
exactly the left quantization of the corresponding base derivative. -/
theorem firstOrderAction_direction_commutator_of_jointSmooth {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (Function.uncurry a))
    (f : SchwartzMap E ℂ) (x e : E) :
    deriv (fun t : ℝ => firstOrderAction a f (x + t • e)) 0 -
      firstOrderAction a (SchwartzMap.pderivCLM ℂ e f) x =
      firstOrderAction (baseDirectionSymbol a e) f x :=
  firstOrderAction_direction_commutator ha (baseDirectionSymbol_continuous hs) f x e

end Burnett.Analysis.FirstOrderDyadic
