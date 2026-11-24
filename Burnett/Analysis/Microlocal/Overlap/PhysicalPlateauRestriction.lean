import Burnett.Analysis.Microlocal.Overlap.CommonPhysicalBasePlateau
import Burnett.Analysis.Microlocal.Overlap.NormalizedCotangentPhysicalMeasure
import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalMeasureOverlap
import Burnett.Analysis.Microlocal.Overlap.PhysicalMeasureRestriction

/-! Chart-normalized measures have compatible restrictions on actual plateaus. -/

set_option autoImplicit false
set_option maxHeartbeats 190000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay continuous_chartAuxiliaryRay)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovectors (roundOverlap measurableSet_roundOverlap)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

theorem map_sourcePhysicalPlateauMeasure_eq_restrict_normalized
    (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v)) :
    (sourcePhysicalPlateauMeasure p r B νq hfq hn).map (fun z => chartAuxiliaryRay r q z.1) =
      (normalizedCotangentPhysicalMeasure q r B hn νq hfq).restrict (commonPatchCotangentPlateau p) := by
  let U := roundOverlap q d
  let P := commonPatchCotangentPlateau p
  let S := chartAuxiliaryRay r q ⁻¹' P
  let μ := chartPhysicalJetMeasure r B hn q νq hfq
  have hRay := (continuous_chartAuxiliaryRay r q).measurable
  have hP : MeasurableSet P := measurableSet_commonPatchCotangentPlateau p
  have hS : MeasurableSet S := hRay hP
  have hSubset : S ⊆ U := by
    dsimp only [S, P, U]
    rw [chartAuxiliaryRay_preimage_source_commonPatchPlateau p r]
    exact sourcePlateau_subset_roundOverlap p
  have hPreimage : (Subtype.val : U → Chart q.ball) ⁻¹' S = sourceRoundPlateau p := by
    dsimp only [S, P]
    rw [chartAuxiliaryRay_preimage_source_commonPatchPlateau p r]
    rfl
  have h := map_comap_subtype_coe_restrict_withDensity μ (chartInverseCutoffSquare q)
    (measurableSet_roundOverlap q d) hS hSubset
  rw [hPreimage] at h
  have hMap := congrArg (fun m : Measure (Chart q.ball) => m.map (chartAuxiliaryRay r q)) h
  dsimp only at hMap
  rw [Measure.map_map hRay measurable_subtype_coe] at hMap
  rw [sourcePhysicalPlateauMeasure_eq_invCutoff p r B νq hfq hn,
    normalizedCotangentPhysicalMeasure, Measure.restrict_map hRay hP]
  exact hMap

theorem map_targetPhysicalPlateauMeasure_eq_restrict_normalized
    (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v)) :
    (targetPhysicalPlateauMeasure p r B νd hfd hn).map (chartAuxiliaryRay r d) =
      (normalizedCotangentPhysicalMeasure d r B hn νd hfd).restrict (commonPatchCotangentPlateau p) := by
  have hRay := (continuous_chartAuxiliaryRay r d).measurable
  have hP := measurableSet_commonPatchCotangentPlateau p
  rw [targetPhysicalPlateauMeasure_eq_invCutoff p r B νd hfd hn,
    normalizedCotangentPhysicalMeasure, Measure.restrict_map hRay hP,
    chartAuxiliaryRay_preimage_target_commonPatchPlateau p r,
    restrict_withDensity p.measurableSet_targetPhasePlateau]
  rfl

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On the actual compact base plateau both normalized chart measures have
the same restriction in the cotangent bundle. -/
theorem originalVacuum_normalizedCotangentPhysicalMeasure_restrict_commonPatch
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) :
    (normalizedCotangentPhysicalMeasure q r B hSig.isNondegenerate νq hfq).restrict
        (commonPatchCotangentPlateau p) =
      (normalizedCotangentPhysicalMeasure d r B hSig.isNondegenerate νd hfd).restrict
        (commonPatchCotangentPlateau p) := by
  rw [← map_sourcePhysicalPlateauMeasure_eq_restrict_normalized p r B hSig.isNondegenerate νq hfq,
    ← map_targetPhysicalPlateauMeasure_eq_restrict_normalized p r B hSig.isNondegenerate νd hfd]
  exact originalVacuum_commonPatch_cotangentPhysicalMeasure_eq r B g hB hg hSig hsG hnG hconv hb hv
    q d x p σ hσ νq hfq νd hfd hRq hRd

end Burnett.Microlocal.Overlap
