import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalPhysicalMeasure
import Burnett.Geometry.Cotangent.CosphereMeasure

/-! Place the glued original measure on the actual auxiliary unit section. -/

set_option autoImplicit false
set_option maxHeartbeats 290000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open Burnett.Geometry.UnitCosphere
  (Cosphere projection hamiltonian fromAmbient fromAmbient_locallyFinite fromAmbient_regular
    fromAmbient_finiteOnCompactBase fromAmbient_offNull map_fromAmbient_eq_of_unitNull)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The same global physical measure lies on the actual full auxiliary unit
cosphere and retains its law on every represented nonzero chart locus. -/
theorem exists_originalVacuum_physicalMeasure_on_cosphere
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ μ : Measure (Cosphere r),
      IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
      (∀ K : Set M, IsCompact K → μ (projection ⁻¹' K) < ⊤) ∧
      μ {p | hamiltonian B hSig.isNondegenerate p ≠ 0} = 0 ∧
      ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfq : ∀ v, IsFiniteMeasure (νq v)),
        RepresentsCompactJetPairings q.ball
          (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
            (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) νq hfq →
        (μ.map (Subtype.val : Cosphere r → CotangentBundle M)).restrict
            ((fun y : CotangentBundle M => y.proj) ⁻¹' q.nonzeroLocus) =
          (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict
            ((fun y : CotangentBundle M => y.proj) ⁻¹' q.nonzeroLocus) := by
  obtain ⟨t, ht, μ, hLoc, hReg, hNull, hFinite, hPatch⟩ :=
    exists_originalVacuum_globalPhysicalMeasure_and_chartLaw r B g hB hg hSig hsG hnG hconv hb hv s hs
  letI : IsLocallyFiniteMeasure μ := hLoc
  letI : μ.Regular := hReg
  refine ⟨t, ht, fromAmbient r μ, fromAmbient_locallyFinite r μ,
    fromAmbient_regular r B hSig.isNondegenerate μ hNull,
    fromAmbient_finiteOnCompactBase r μ hFinite,
    fromAmbient_offNull r B hSig.isNondegenerate μ hNull, ?_⟩
  intro q νq hfq hRep
  rw [map_fromAmbient_eq_of_unitNull r B hSig.isNondegenerate μ hNull]
  exact hPatch q νq hfq hRep

end Burnett.Microlocal.Overlap
