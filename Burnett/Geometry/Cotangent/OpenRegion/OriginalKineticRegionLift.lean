import Burnett.Analysis.TransportClosure.OriginalKineticAssembly
import Burnett.Geometry.Cotangent.OpenRegion.GloballyHyperbolicLift

set_option autoImplicit false

noncomputable section

namespace Burnett.C04

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open UnitNullCompactness CotangentAngularExtension ActualTestLift FiniteCausalVolume OpenRegion
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian)
open Burnett.Microlocal.Overlap (HasCosphereEinsteinMoments)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel

/-- The ambient original cosphere equation supplies the full momentum
equations on each globally hyperbolic open region for that same measure. -/
theorem originalKineticMeasure_has_openRegion_lifts
    (r : Metric (M := M)) (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (μ : Measure (Cosphere r)) [IsLocallyFiniteMeasure μ]
    (hNull : μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0)
    (hMom : HasCosphereEinsteinMoments r B hSig.isNondegenerate μ)
    (hTransport : HasOriginalCosphereTransport r B μ) :
    ∀ (U : Opens M) (o : TimeOrientation (restrictBilinear U B)),
      ChartGlobalHyperbolicity o →
      ∃ ν : Measure (puncturedCotangent (M := U)), HasLiftedRegionEinsteinEquations U r B hSig μ ν := by
  intro U o hGH
  apply exists_openRegionEinsteinLift_of_chartGlobalHyperbolicity U r B hB hSig o hGH μ hNull hMom
  intro f hf hHom hSupport
  obtain ⟨K, hK, hSub⟩ := hSupport
  have hTest : IsDegreeOneTransportTest f := ⟨hf, hHom, K, hK, fun p _ hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp (hSub h))⟩
  exact (hTransport f hTest).2

end Burnett.C04
