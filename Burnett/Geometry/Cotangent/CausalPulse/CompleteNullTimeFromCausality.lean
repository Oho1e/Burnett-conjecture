import Burnett.Geometry.Causality.CausalVolumeTimeOnPaths
import Burnett.Geometry.Cotangent.CausalPulse.CanonicalOrbitCompleteness

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.CausalOrbitPulse

open scoped ContDiff Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.FiniteCausalVolume

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M]

/-- Compact causal diamonds and strong causality give one continuous
time with full range on every actual maximal punctured null trajectory. -/
theorem exists_completeNullTime_of_chartGlobalHyperbolicity
    (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation g) (hGH : ChartGlobalHyperbolicity o) :
    ∃ T : M → ℝ, Continuous T ∧ HasCompleteNullTime T g hg hL.isNondegenerate hL.isSymmetric := by
  obtain ⟨T, hT, hPath⟩ := exists_continuous_completeCausalVolumeTime hg hL o hGH
  exact ⟨T, hT, hasCompleteNullTime_of_complete_regular_causal_paths g hg hL T hPath⟩

end Burnett.Geometry.CausalOrbitPulse
