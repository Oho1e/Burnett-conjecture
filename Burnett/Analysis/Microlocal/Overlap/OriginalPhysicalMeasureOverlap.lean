import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalJetMeasure
import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalPlateauMeasure

/-! The same original positive physical measures agree on common plateaus. -/

set_option autoImplicit false
set_option maxHeartbeats 460000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay continuous_chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovectors
  (roundOverlap continuous_roundOverlapTransition chartAuxiliaryRay_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- The normalized positive measures from the two original chart witnesses
on one subsequence agree under the real phase transition. -/
theorem originalVacuum_commonPatch_physicalPlateauMeasure_map_eq
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q d : CompactChartInput M) (x : CoordinateSpace)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    (sourcePhysicalPlateauMeasure p r B νq hfq hSig.isNondegenerate).map (transportedRoundPoint q d) =
      targetPhysicalPlateauMeasure p r B νd hfd hSig.isNondegenerate := by
  apply original_commonPatch_physicalPlateauMeasure_map_eq r B g hB hg
    hSig.isSymmetric hSig.isNondegenerate hconv hb q d x p σ hσ νq hfq νd hfd hRq hRd
  · exact ae_original_chartPhysicalJetContraction_nonneg_real r B g hB hg hSig hsG hnG hconv hb hv
      q σ hσ νq hfq hRq
  · exact ae_original_chartPhysicalJetContraction_nonneg_real r B g hB hg hSig hsG hnG hconv hb hv
      d σ hσ νd hfd hRd

variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

omit [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M] in
private theorem map_chartAuxiliaryRay_eq_of_roundOverlapMap (r : Metric (M := M))
    (q d : CompactChartInput M) (μq : Measure (roundOverlap q d)) (μd : Measure (Chart d.ball))
    (h : μq.map (transportedRoundPoint q d) = μd) :
    μq.map (fun z => chartAuxiliaryRay r q z.1) = μd.map (chartAuxiliaryRay r d) := by
  have hT : Measurable (transportedRoundPoint q d) :=
    (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable
  rw [← h, Measure.map_map (continuous_chartAuxiliaryRay r d).measurable hT]
  congr 1
  funext z
  exact (chartAuxiliaryRay_roundOverlapTransition r q d z).symm

/-- Both normalized original physical measures represent the same measure
of the actual auxiliary cotangent rays on the common plateaus. -/
theorem originalVacuum_commonPatch_cotangentPhysicalMeasure_eq
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (q d : CompactChartInput M) (x : CoordinateSpace)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    (sourcePhysicalPlateauMeasure p r B νq hfq hSig.isNondegenerate).map
        (fun z => chartAuxiliaryRay r q z.1) =
      (targetPhysicalPlateauMeasure p r B νd hfd hSig.isNondegenerate).map
        (chartAuxiliaryRay r d) :=
  map_chartAuxiliaryRay_eq_of_roundOverlapMap r q d _ _
    (originalVacuum_commonPatch_physicalPlateauMeasure_map_eq r B g hB hg hSig hsG hnG hconv hb hv
      q d x p σ hσ νq hfq νd hfd hRq hRd)

end Burnett.Microlocal.Overlap
