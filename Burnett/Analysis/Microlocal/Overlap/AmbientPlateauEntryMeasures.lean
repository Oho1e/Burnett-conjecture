import Burnett.Analysis.Microlocal.Overlap.AmbientPlateauNormalization
import Burnett.Analysis.Microlocal.Overlap.CommonPatchAmbientEntries

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovariantGradient (overlapJetCoefficient)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On a common patch, dividing each original matrix density by the square
of its own chart cutoff gives the chart change law on ambient Borel sets.
All coefficients are the actual three-slot chart change coefficients. -/
theorem commonPatch_normalized_ambientEntryMeasures
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (q d : CompactChartInput M) (x : E)
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
    (S : Set (Chart d.ball)) (hS : MeasurableSet S) (i j : JetSlot) :
    (∫ z in p.sourcePhasePlateauPreimage S,
      (((((q.cutoff : E → ℝ) z.1)⁻¹) ^ 2 : ℝ) : ℂ) * density νq hfq z i j ∂traceMeasure νq) =
    ∫ y in S ∩ p.targetPhasePlateau, ∑ k : JetSlot, ∑ l : JetSlot,
      conj (↑(overlapJetCoefficient q.center d.center i k y.1) : ℂ) *
        (↑(overlapJetCoefficient q.center d.center j l y.1) : ℂ) *
        (((((d.cutoff : E → ℝ) y.1)⁻¹) ^ 2 : ℝ) : ℂ) * density νd hfd y k l ∂traceMeasure νd := by
  obtain ⟨w, hw, he⟩ := exists_commonPatch_ambientEntryMeasures r B g hB hg hnB hconv hbnd
    q d x p σ hσ νq hfq νd hfd hRq hRd
  exact normalized_ambientEntries_of_commonPatch_factors q d x p νq hfq νd hfd w hw he S hS i j

end Burnett.Microlocal.Overlap
