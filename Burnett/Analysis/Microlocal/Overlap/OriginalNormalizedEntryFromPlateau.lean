import Burnett.Analysis.Microlocal.Overlap.AmbientPlateauEntryMeasures
import Burnett.Analysis.Microlocal.Overlap.InverseEntryToVector
import Burnett.Geometry.AuxiliaryAdmissibility

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
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Both original ambient chart witnesses stay fixed on the same subsequence.
The local ordered entry measures transport across the genuine round phase map. -/
theorem original_commonPatch_normalized_roundJetMeasure
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M) (x : CoordinateSpace)
    (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd) (i j : JetSlot) :
    ((sourcePlateauTrace p νq).withDensityᵥ
        (fun z => sourceNormalizedDensity p νq hfq i j z.1)).map (transportedRoundPoint q d) =
      ((traceMeasure νd).restrict p.targetPhasePlateau).withDensityᵥ
        (targetTransformedDensity p νd hfd i j) := by
  apply normalizedEntryMeasure_of_inverseCutoffBorel q d x p νq hfq νd hfd i j
  intro S hS
  exact commonPatch_normalized_ambientEntryMeasures r B g hB hg hnB hconv hbnd
    q d x p σ hσ νq hfq νd hfd hRq hRd S hS i j

end Burnett.Microlocal.Overlap
