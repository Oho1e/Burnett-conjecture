import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactBaseFourierModes

set_option autoImplicit false
set_option maxHeartbeats 4800000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Finset
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff ENNReal Topology BigOperators

/-- Ordinary order-zero bounds in a fixed chart, in the mixed jet
convention used by the paper's compact spatial expansion. -/
structure RadianOrderZeroSymbolSeminorms (r : E → E → ℂ) : Prop where
  jets : CompactBaseFrequencyJets r univ
  estimate : ∀ n m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    (1+‖ξ‖)^n * ‖iteratedFDeriv ℝ m (fun y => iteratedFDeriv ℝ n (r y) ξ) x‖ ≤ C

end Burnett.A03
