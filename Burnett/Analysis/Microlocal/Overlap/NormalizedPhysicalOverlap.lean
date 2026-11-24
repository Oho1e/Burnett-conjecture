import Burnett.Analysis.Microlocal.Overlap.PhysicalPlateauRestriction
import Burnett.Analysis.Microlocal.PhysicalChartCover

/-! Extend compact-plateau compatibility over the full nonzero overlap. -/

set_option autoImplicit false
set_option maxHeartbeats 210000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricSequence
open Burnett.Geometry.UnitNullCompactness (CotangentBundle)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.OverlapWindows
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable (q d : CompactChartInput M)

private theorem nonzeroOverlap_eq_image :
    q.nonzeroLocus ∩ d.nonzeroLocus =
      (chartAt CoordinateSpace q.center).symm ''
        nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff := by
  ext m
  let eq := chartAt CoordinateSpace q.center
  let ed := chartAt CoordinateSpace d.center
  constructor
  · rintro ⟨hq, hd⟩
    have hqS : m ∈ eq.source := hq.1
    have hdS : m ∈ ed.source := hd.1
    have hPoint : eq.symm (eq m) = m := eq.left_inv hqS
    have hT : chartTransition q.center d.center (eq m) = ed m := by
      change ed (eq.symm (eq m)) = ed m
      rw [hPoint]
    have hSrc : eq m ∈ (chartTransition q.center d.center).source := by
      refine ⟨eq.map_source hqS, ?_⟩
      change eq.symm (eq m) ∈ ed.source
      rwa [hPoint]
    refine ⟨eq m, ⟨⟨hSrc, ?_⟩, ⟨q.chart_mem_interior_of_mem_nonzeroLocus hq, hq.2⟩⟩, hPoint⟩
    change chartTransition q.center d.center (eq m) ∈
      interior d.ball.closedBall ∩ Function.support (d.cutoff : CoordinateSpace → ℝ)
    rw [hT]
    exact ⟨d.chart_mem_interior_of_mem_nonzeroLocus hd, hd.2⟩
  · rintro ⟨y, hy, rfl⟩
    have hqT : y ∈ eq.target := hy.1.1.1
    have hqS := eq.symm_mapsTo hqT
    refine ⟨⟨hqS, ?_⟩, ⟨hy.1.1.2, hy.1.2.2⟩⟩
    change eq (eq.symm y) ∈ Function.support (q.cutoff : CoordinateSpace → ℝ)
    rw [eq.right_inv hqT]
    exact hy.2.2

private theorem nonzeroOverlap_eq_union_commonPlateaus
    (p : ∀ y : nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff,
      CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff y.1)
    (centers : Set (nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff))
    (cover : nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff =
      ⋃ y ∈ centers, Metric.ball y.1 ((p y).sourceRadius / 2)) :
    q.nonzeroLocus ∩ d.nonzeroLocus = ⋃ y ∈ centers, commonPatchBasePlateau (p y) := by
  have hClosed : nonzeroCutoffOverlap q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff =
      ⋃ y ∈ centers, Metric.closedBall y.1 ((p y).sourceRadius / 2) := by
    refine Subset.antisymm (cover.le.trans (iUnion₂_mono fun _ _ => Metric.ball_subset_closedBall)) ?_
    refine iUnion₂_subset fun y _ => ?_
    have hRadius : (p y).sourceRadius / 2 ≤ (p y).sourceRadius := by
      linarith [(p y).sourceRadius_pos]
    exact (Metric.closedBall_subset_closedBall hRadius).trans (p y).sourceWindow_subset_nonzeroCutoffOverlap
  calc
    _ = _ := nonzeroOverlap_eq_image q d
    _ = (chartAt CoordinateSpace q.center).symm ''
        (⋃ y ∈ centers, Metric.closedBall y.1 ((p y).sourceRadius / 2)) :=
      congrArg (fun s => (chartAt CoordinateSpace q.center).symm '' s) hClosed
    _ = _ := by simp only [image_iUnion, commonPatchBasePlateau]

variable [IsManifold Model ∞ M] [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The normalized measures from the original witnesses have the same
restriction over the entire base overlap where both cutoffs are nonzero. -/
theorem originalVacuum_normalizedCotangentPhysicalMeasure_restrict_overlap
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
        ((fun x : CotangentBundle M => x.proj) ⁻¹' (q.nonzeroLocus ∩ d.nonzeroLocus)) =
      (normalizedCotangentPhysicalMeasure d r B hSig.isNondegenerate νd hfd).restrict
        ((fun x : CotangentBundle M => x.proj) ⁻¹' (q.nonzeroLocus ∩ d.nonzeroLocus)) := by
  obtain ⟨p, centers, hCountable, hCover⟩ :=
    exists_countable_commonCutoffPatches q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff
  rw [nonzeroOverlap_eq_union_commonPlateaus q d p centers hCover]
  simp only [preimage_iUnion]
  apply (Measure.restrict_biUnion_congr hCountable).2
  intro y _
  exact originalVacuum_normalizedCotangentPhysicalMeasure_restrict_commonPatch (p y)
    r B g hB hg hSig hsG hnG hconv hb hv σ hσ νq hfq νd hfd hRq hRd

end Burnett.Microlocal.Overlap
