import Burnett.Analysis.TransportWard.Weyl.OriginalChartTwoScaleAssembly
import Burnett.Analysis.TransportClosure.OriginalKineticAssembly
import Burnett.Analysis.TransportClosure.OriginalRepresentedCoverTransport

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4200

noncomputable section

namespace Burnett.C04

open Set MeasureTheory
open scoped ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open UnitNullCompactness
open Burnett.Geometry.ActualTestLift (actualHamiltonDerivative)
open Burnett.Geometry.UnitCosphere (Cosphere projection hamiltonian)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.V03.Palatini (HasOriginalFrozenC03Tail originalChartWeyl_twoScale_of_frozenC03_tail)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The supplied-patch tail gives transport for the original physical measure
on its already represented subsequence. -/
theorem originalVariationalTransport_of_actualFrozenTail
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
    (hFinite : ∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤)
    (hFrozen : ∀ (q : CompactChartInput M) (ν : (JetSlot → ℂ) → Measure (Chart q.ball))
      (hf : ∀ v, IsFiniteMeasure (ν v)),
      RepresentsCompactJetPairings q.ball
        (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)) σ ν hf →
      Burnett.P01.RepresentsVolumeProjectedPairings B g q σ ν hf →
      ∀ f : CotangentBundle M → ℝ, IsDegreeOneTransportTest f → IsAntipodallyOdd f →
      HasCompactTransportBaseSupportIn f (q.cutoffLocusAbove (1 / 2)) →
      HasOriginalFrozenC03Tail B g hB hg σ q.center f) :
    HasOriginalCosphereTransport r B μ := by
  have hTransport := originalTransport_of_representedCover_twoScale_bounds r B g hB hg hSig
    (fun n => (hSigG n).isSymmetric) (fun n => (hSigG n).isNondegenerate)
    hconv hb hv σ hσ A μ hA hPhysical hNull hFinite
    (fun q ν hf hRep hProj f hTest hOdd hSupport =>
      originalChartWeyl_twoScale_of_frozenC03_tail r B g hB hSig hg hSigG hconv hb hv
        σ hσ A hA hReceive μ hPhysical q ν hf hRep f hTest hOdd hSupport
        (hFrozen q ν hf hRep hProj f hTest hOdd hSupport))
  intro f hf
  have hEq : (fun p : Cosphere r => actualHamiltonDerivative B f p.val) =
      (fun p : Cosphere r => basePointHamiltonDerivative B hSig.isNondegenerate f p.val) :=
    funext fun p => actualHamiltonDerivative_eq_basePointHamiltonDerivative r B hSig.isNondegenerate
      hSig.isSymmetric f hf.1 p
  rw [hEq]
  exact hTransport f hf

end Burnett.C04
