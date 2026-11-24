import Burnett.Analysis.Microlocal.Overlap.OriginalPhysicalPlateauConsumer
import Burnett.Analysis.Microlocal.Overlap.PhysicalPlateauMeasures

/-! The original Borel overlap theorem transports the normalized positive measures. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OverlapCovectors (roundOverlap)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped BigOperators ContDiff Manifold

private theorem cutoff_mul_contraction {J : Type*} [Fintype J]
    (w ρ : J → J → ℂ) (f : ℂ) :
    (∑ i, ∑ j, w i j * (f * ρ i j)) = f * (∑ i, ∑ j, w i j * ρ i j) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ac_rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

section Contractions

variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)
variable (r : Metric (M := M)) (B : Field (M := M))
variable (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
variable (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))

private theorem sourcePhysicalPlateauDensity_eq_contraction (z : roundOverlap q d) :
    sourcePhysicalPlateauDensity p r B νq hfq z =
      ∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B q.center z.1.1 i j : ℂ) *
        sourceNormalizedDensity p νq hfq i j z.1 := by
  unfold sourcePhysicalPlateauDensity sourceNormalizedDensity chartPhysicalJetContraction
  exact (cutoff_mul_contraction _ _ _).symm

private theorem targetPhysicalPlateauDensity_eq_contraction (y : Chart d.ball) :
    targetPhysicalPlateauDensity p r B νd hfd y =
      ∑ i : JetSlot, ∑ j : JetSlot, (chartPhysicalJetWeight r B d.center y.1 i j : ℂ) *
        (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ) * density νd hfd y i j := by
  unfold targetPhysicalPlateauDensity chartPhysicalJetContraction
  simpa only [mul_assoc] using (cutoff_mul_contraction
    (fun i j => (chartPhysicalJetWeight r B d.center y.1 i j : ℂ))
    (fun i j => density νd hfd y i j) (((p.targetFactor : CoordinateSpace → ℝ) y.1 ^ 2 : ℝ) : ℂ)).symm

end Contractions

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- On one original subsequence, the two normalized finite positive null-shell
measures obey the actual round overlap transformation. The positivity inputs
are the nonnegative real values of the original contractions on the same trace
measures. -/
theorem original_commonPatch_physicalPlateauMeasure_map_eq
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
    (hPosq : ∀ᵐ z ∂(traceMeasure νq).restrict (chartAuxiliaryNull r B hnB q),
      0 ≤ (chartPhysicalJetContraction r B q νq hfq z).re ∧
        (chartPhysicalJetContraction r B q νq hfq z).im = 0)
    (hPosd : ∀ᵐ z ∂(traceMeasure νd).restrict (chartAuxiliaryNull r B hnB d),
      0 ≤ (chartPhysicalJetContraction r B d νd hfd z).re ∧
        (chartPhysicalJetContraction r B d νd hfd z).im = 0) :
    (sourcePhysicalPlateauMeasure p r B νq hfq hnB).map (transportedRoundPoint q d) =
      targetPhysicalPlateauMeasure p r B νd hfd hnB := by
  apply physicalPlateauMeasure_map_eq_of_setIntegral p r B νq hfq νd hfd hB hsB hnB hPosq hPosd
  intro S hS
  have h := original_commonPatch_physicalPlateauTest r B g hB hg hsB hnB hconv hbnd q d x p
    σ hσ νq hfq νd hfd hRq hRd (fun _ => 1) measurable_const 1 zero_le_one (by simp) S hS
  simpa only [one_mul, ← sourcePhysicalPlateauDensity_eq_contraction p r B νq hfq,
    ← targetPhysicalPlateauDensity_eq_contraction p r B νd hfd] using h

end Burnett.Microlocal.Overlap
