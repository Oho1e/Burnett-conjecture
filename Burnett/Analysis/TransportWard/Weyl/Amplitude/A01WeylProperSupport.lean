import Burnett.Analysis.TransportWard.Weyl.Amplitude.A01WeylBandRegularity

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff ENNReal Topology BigOperators

/-- Low frequency plus the first N actual bands of the same order-one symbol. -/
def a01CompleteFiniteKernel (a : E → E → ℂ) (N : ℕ) (q : E × E) : ℂ :=
  firstOrderLowKernel a q.1 q.2 + ∑ j ∈ Finset.range N, firstOrderAnnularKernel a q.1 j q.2

end Burnett.A03
