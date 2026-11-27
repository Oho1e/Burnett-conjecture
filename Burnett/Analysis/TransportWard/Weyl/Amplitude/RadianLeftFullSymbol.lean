import Burnett.Analysis.TransportWard.Weyl.PatchFourierPhase

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform

/-- Literal left quantization at the original radian frequency of a
possibly complex full symbol. -/
def radianLeftQuantization (a : E → E → ℂ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ ξ : E, patchFourierPhase ξ x * a x (tau • ξ) * 𝓕 (u : E → ℂ) ξ

end Burnett.A03
