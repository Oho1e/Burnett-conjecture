import Burnett.Analysis.TransportWard.Weyl.PatchFourierPhase
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff

/-- Actual physical action of a two-point kernel. -/
def compactKernelAction (K : E → E → ℂ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ y : E, K x y * u y

end Burnett.A03
