import Burnett.Analysis.Microlocal.Overlap.NormalizedEntryTransport

/-! Consume the original-sequence overlap theorem as an ordered measure identity. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.F05.OverlapCovectors
  (roundOverlap measurableSet_roundOverlap continuous_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
theorem normalizedEntryMeasure_of_inverseCutoffBorel
    (q d : CompactChartInput M) (x : CoordinateSpace)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (i j : JetSlot)
    (hEntry : ∀ S : Set (Chart d.ball), MeasurableSet S →
    (∫ z in p.sourcePhasePlateauPreimage S,
      (((((q.cutoff : E → ℝ) z.1)⁻¹) ^ 2 : ℝ) : ℂ) * density νq hfq z i j ∂traceMeasure νq) =
    ∫ y in S ∩ p.targetPhasePlateau, ∑ k : JetSlot, ∑ l : JetSlot,
      conj (↑(overlapJetCoefficient q.center d.center i k y.1) : ℂ) *
        (↑(overlapJetCoefficient q.center d.center j l y.1) : ℂ) *
        (((((d.cutoff : E → ℝ) y.1)⁻¹) ^ 2 : ℝ) : ℂ) * density νd hfd y k l ∂traceMeasure νd) :
    ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j) := by
  apply map_normalizedEntry_eq_target_of_borel p νq hfq νd hfd i j
  intro S hS
  have hT : Measurable (transportedRoundPoint q d) :=
    (continuous_subtype_val.comp (continuous_roundOverlapTransition q d)).measurable
  have hP : MeasurableSet (sourceRoundPlateau p) :=
    (continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).measurable
      Metric.isClosed_closedBall.measurableSet
  have hDom : (Subtype.val : roundOverlap q d → Chart q.ball) ''
      ((transportedRoundPoint q d ⁻¹' S) ∩ sourceRoundPlateau p) = p.sourcePhasePlateauPreimage S := by
    rw [inter_comm]
    rfl
  have hSource : MeasurableSet (p.sourcePhasePlateauPreimage S) := by
    rw [← hDom]
    exact (MeasurableEmbedding.subtype_coe (measurableSet_roundOverlap q d)).measurableSet_image.mpr
      ((hT hS).inter hP)
  rw [hDom]
  have hC := hEntry S hS
  convert hC using 1
  · apply setIntegral_congr_fun hSource
    rintro _ ⟨z, hz, rfl⟩
    exact congrArg (fun t : ℝ => ((t ^ 2 : ℝ) : ℂ) * density νq hfq z.1 i j)
      (p.sourceFactor_on_halfBall hz.1)
  · apply setIntegral_congr_fun (hS.inter p.measurableSet_targetPhasePlateau)
    intro y hy
    simp only [targetTransformedDensity, p.targetFactor_on_targetPlateau hy.2]

end Burnett.Microlocal.Overlap
