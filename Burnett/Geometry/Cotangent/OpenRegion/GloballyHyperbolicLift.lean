import Burnett.Geometry.Cotangent.OpenRegion.PulseEinsteinLift
import Burnett.Geometry.Cotangent.CausalPulse.CompleteNullTimeFromCausality

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear UnitNullCompactness
open CotangentAngularExtension ActualTestLift FiniteCausalVolume CausalOrbitPulse
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel

/-- The original ambient transported Einstein measure has a full null lift
on every open region with compact causal diamonds and strong causality. -/
theorem exists_openRegionEinsteinLift_of_chartGlobalHyperbolicity
    (U : Opens M) (r : Metric (M := M)) (g : Field (M := M))
    (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation (restrictBilinear U g)) (hGH : ChartGlobalHyperbolicity o)
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian g hL.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r g hL.isNondegenerate μ)
    (hTransport : ∀ a : CotangentBundle M → ℝ,
      ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent →
      (∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p) →
      (∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) →
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0) :
    ∃ ν : Measure (puncturedCotangent (M := U)), HasLiftedRegionEinsteinEquations U r g hL μ ν := by
  obtain ⟨T, hTc, hT⟩ := exists_completeNullTime_of_chartGlobalHyperbolicity (restrictBilinear U g)
    (isSmooth_restrictBilinear U g hg) (hasLorentzSignature_restrictBilinear U hL) o hGH
  exact exists_openRegionEinsteinLift_of_completeNullTime U r g hg hL T hTc hT μ hNull hMom hTransport

end Burnett.Geometry.OpenRegion
