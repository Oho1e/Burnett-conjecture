import Burnett.Analysis.TransportClosure.OriginalVariationalTransport
import Burnett.Geometry.Cotangent.OpenRegion.OriginalKineticRegionLift
import Burnett.Analysis.TransportWard.Weyl.OriginalFrozenC03Tail

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.C04

open Set MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitNullCompactness CotangentAngularExtension ActualTestLift FiniteCausalVolume OpenRegion IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian FixedChartNaturality)
open Burnett.Microlocal.Overlap
open Burnett.V03.Palatini (hasOriginalFrozenC03Tail_of_originalChartWard)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

attribute [local instance] puncturedMeasurable puncturedBorel

/-- Transport for the original quadratic measure on the already fixed
subsequence and intrinsic amplitude, for every original transport test. -/
theorem originalVariationalTransport
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r))
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hReceive : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (hPhysical : HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ)
    (hNull : μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0)
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) :
    HasOriginalCosphereTransport r B μ := by
  apply originalVariationalTransport_of_actualFrozenTail r B g hB hg hSig hSigG hv hconv hb
    σ hσ A μ hA hReceive hPhysical hNull hFinite
  intro q ν hf _ _ f hTest hOdd hSupport
  obtain ⟨K, hK, hLoc, hOff⟩ := hSupport
  have hChart : K ⊆ (chartAt CoordinateSpace q.center).source := by
    intro x hx
    exact ((q.cutoffLocusAbove_subset_nonzeroLocus (by norm_num)) (hLoc hx)).1
  exact hasOriginalFrozenC03Tail_of_originalChartWard r B g hB hSig hg
    (fun n => (hSigG n).isSymmetric) hconv hb σ hσ A hA hReceive q.center f hTest hOdd K hK hChart hOff

/-- The original smooth-limit kinetic theorem, with one quadratic measure
also satisfying transport and furnishing the lift on every globally
hyperbolic open region. -/
theorem exists_originalForwardKineticMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hSigG : ∀ n, HasLorentzSignature (g n))
    (hTime : ∃ V : ChartVectorField.Field (M := M), ChartVectorField.IsSmooth V ∧ ∀ x, B x (V x) (V x) < 0)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ (A : IntrinsicAmplitudeCovariance r) (μ : Measure (Cosphere r)),
        HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A ∧
        HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
        IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
        (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
        μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
        HasCosphereEinsteinMoments r B hSig.isNondegenerate μ ∧
        (∀ x, intrinsicScalar B hSig.isNondegenerate x = 0) ∧ FixedChartNaturality μ ∧
        HasOriginalCosphereTransport r B μ ∧
        (∀ (U : Opens M) (o : TimeOrientation (restrictBilinear U B)),
          ChartGlobalHyperbolicity o →
          ∃ ν : Measure (puncturedCotangent (M := U)), HasLiftedRegionEinsteinEquations U r B hSig μ ν) := by
  obtain ⟨σ, hσ, A, μ, hA, hReceive, _, _, _, _, hPhysical, hFin, hReg, hCompact, hNull,
    hMom, hScalar, hNature⟩ := F07.exists_quadraticOriginalMeasure r B g hB hg hSig hSigG hTime hv hconv hb
  have hTransport := originalVariationalTransport r B g hB hg hSig hSigG hv hconv hb
    σ hσ A μ hA hReceive hPhysical hNull hCompact
  letI := hFin
  exact ⟨σ, hσ, A, μ, hA, hPhysical, hFin, hReg, hCompact, hNull, hMom, hScalar, hNature, hTransport,
    originalKineticMeasure_has_openRegion_lifts r B hB hSig μ hNull hMom hTransport⟩

end Burnett.C04
