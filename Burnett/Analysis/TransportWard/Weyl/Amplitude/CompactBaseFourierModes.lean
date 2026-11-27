import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 2900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open scoped ContDiff Topology BigOperators

local notation "E" => CoordinateSpace

/-- Frequency jets used in the Fourier coefficients of a compact-base
symbol. The frequency domain can be the punctured space or all of space. -/
structure CompactBaseFrequencyJets (a : E → E → ℂ) (U : Set E) : Prop where
  frequencySmooth : ∀ x, ContDiffOn ℝ ∞ (a x) U
  baseJetSmooth : ∀ n : ℕ, ∀ ξ ∈ U, ContDiff ℝ ∞ (fun x => iteratedFDeriv ℝ n (a x) ξ)
  jointJetContinuous : ∀ n : ℕ,
    ContinuousOn (fun p : E × E => iteratedFDeriv ℝ n (a p.1) p.2) ((univ : Set E) ×ˢ U)

end Burnett.A03
