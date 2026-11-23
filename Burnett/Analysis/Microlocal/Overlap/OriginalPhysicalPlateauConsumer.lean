import Burnett.Analysis.Microlocal.Overlap.OriginalNormalizedEntryFromPlateau
import Burnett.Analysis.Microlocal.Overlap.PhysicalPlateauTests

/-! Apply the physical scalar contraction to the original overlapping chart witnesses. -/

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The original ambient chart densities on one subsequence give the same
normalized physical test integrals on their common plateau. -/
theorem original_commonPatch_physicalPlateauTest
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hsB : IsSymmetric B) (hnB : IsNondegenerate B)
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
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd)
    (a : Chart d.ball → ℂ) (ha : Measurable a) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ y, ‖a y‖ ≤ C)
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) :
    (∫ z in (transportedRoundPoint q d ⁻¹' S) ∩ (Subtype.val ⁻¹' chartAuxiliaryNull r B hnB q),
      a (transportedRoundPoint q d z) * (∑ i : JetSlot, ∑ j : JetSlot,
        (chartPhysicalJetWeight r B q.center z.1.1 i j : ℂ) * sourceNormalizedDensity p νq hfq i j z.1)
          ∂sourcePlateauTrace p νq) =
      ∫ y in S ∩ chartAuxiliaryNull r B hnB d, a y * (∑ i : JetSlot, ∑ j : JetSlot,
        (chartPhysicalJetWeight r B d.center y.1 i j : ℂ) *
        (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y i j)
          ∂(traceMeasure νd).restrict p.targetPhasePlateau := by
  apply normalizedPhysicalPlateauTest p νq hfq νd hfd r B hB hsB hnB _ a ha C hC hb S hS
  exact fun i j => original_commonPatch_normalized_roundJetMeasure
    r B g hB hg hnB hconv hbnd q d x p σ hσ νq hfq νd hfd hRq hRd i j

end Burnett.Microlocal.Overlap
