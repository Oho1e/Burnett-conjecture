import Burnett.Analysis.Microlocal.Overlap.CommonPatchAmbientOverlap
import Burnett.Analysis.Microlocal.Overlap.CommonPatchCutoffRatios

set_option autoImplicit false
set_option maxHeartbeats 150000

noncomputable section

namespace Burnett.Microlocal.OverlapWindows.CommonCutoffPatch

open Set MeasureTheory
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors (roundOverlap roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.Overlap (sameChartBallInclusion)
open Burnett.Microlocal.SmoothBaseTests (BallData)
open scoped ContDiff Manifold

private theorem mem_range_product_inclusion {X Y : Type*} {U V : Set X} (h : U ⊆ V)
    (z : V × Y) (hz : (z.1 : X) ∈ U) : z ∈ range (Prod.map (Set.inclusion h) id) :=
  ⟨(⟨z.1, hz⟩, z.2), Prod.ext (Subtype.ext rfl) rfl⟩

private theorem mem_range_sameChartBallInclusion {L K : BallData} (h : L.closedBall ⊆ K.closedBall)
    (z : Chart K) (hz : (z.1 : CoordinateSpace) ∈ L.closedBall) :
    z ∈ range (sameChartBallInclusion h) :=
  mem_range_product_inclusion h z hz

private theorem image_preimage_inter_of_lift {A B C D E : Type*}
    (f : A → B) (i : B → C) (j : A → D) (g : D → C) (val : D → E)
    (S V : Set C) (P : Set D)
    (hComm : ∀ a, i (f a) = g (j a))
    (hforward : ∀ a, g (j a) ∈ V → j a ∈ P)
    (hback : ∀ w ∈ P, w ∈ range j ∧ g w ∈ V) :
    (val ∘ j) '' (f ⁻¹' (i ⁻¹' (S ∩ V))) = val '' {w | w ∈ P ∧ g w ∈ S} := by
  ext z
  constructor
  · rintro ⟨a, ha, rfl⟩
    have hmem : g (j a) ∈ S ∩ V := hComm a ▸ ha
    exact ⟨j a, ⟨hforward a hmem.2, hmem.1⟩, rfl⟩
  · rintro ⟨w, ⟨hw, hwS⟩, rfl⟩
    obtain ⟨⟨a, rfl⟩, haV⟩ := hback w hw
    refine ⟨a, ?_, rfl⟩
    change i (f a) ∈ S ∩ V
    rw [hComm a]
    exact ⟨hwS, haV⟩

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

/-- The target plateau viewed in the original target phase space. -/
def targetPhasePlateau : Set (Chart d.ball) :=
  {y | (y.1 : CoordinateSpace) ∈ p.targetPlateau}

theorem measurableSet_targetPhasePlateau : MeasurableSet p.targetPhasePlateau :=
  (continuous_subtype_val.comp continuous_fst).measurable p.isCompact_targetPlateau.isClosed.measurableSet

private theorem targetPhasePlateau_subset_range : p.targetPhasePlateau ⊆ range p.targetPhaseInclusion := by
  intro y hy
  have hyBall : (y.1 : CoordinateSpace) ∈ p.targetInput.ball.closedBall :=
    Metric.ball_subset_closedBall (p.targetPlateau_subset_targetBall hy)
  exact mem_range_sameChartBallInclusion (p.targetInput_ball_subset_interior.trans interior_subset) y hyBall

theorem targetPhaseInclusion_image_preimage_inter_plateau (S : Set (Chart d.ball)) :
    p.targetPhaseInclusion '' (p.targetPhaseInclusion ⁻¹' (S ∩ p.targetPhasePlateau)) =
      S ∩ p.targetPhasePlateau :=
  image_preimage_eq_of_subset (inter_subset_right.trans p.targetPhasePlateau_subset_range)

private theorem sourcePhaseToOverlap_base (z : Chart p.sourceInput.ball) :
    ((p.sourcePhaseToOverlap z).1.1 : CoordinateSpace) = z.1 := by
  rcases z with ⟨⟨y, _⟩, _⟩
  change y = y
  rfl

private theorem sourcePhaseToOverlap_mem_range (w : roundOverlap q d)
    (hw : (w.1.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)) :
    w ∈ range p.sourcePhaseToOverlap := by
  have hsub : Metric.closedBall x (p.sourceRadius / 2) ⊆ p.sourceInput.ball.closedBall :=
    Metric.closedBall_subset_closedBall (show p.sourceRadius / 2 ≤ p.sourceRadius by
      linarith [p.sourceRadius_pos])
  obtain ⟨z, h⟩ := mem_range_sameChartBallInclusion
    (p.sourceInput_ball_subset_interior.trans interior_subset) w.1 (hsub hw)
  exact ⟨z, Subtype.ext h⟩

variable [IsManifold Model ∞ M]

private theorem roundOverlapTransition_base (w : roundOverlap q d) :
    ((roundOverlapTransition q d w).1.1 : CoordinateSpace) = chartTransition q.center d.center w.1.1 :=
  rfl

private theorem sourcePhaseToOverlap_mem_halfBall (z : Chart p.sourceInput.ball)
    (hz : (roundOverlapTransition q d (p.sourcePhaseToOverlap z)).1 ∈ p.targetPhasePlateau) :
    ((p.sourcePhaseToOverlap z).1.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2) := by
  change ((roundOverlapTransition q d (p.sourcePhaseToOverlap z)).1.1 : CoordinateSpace) ∈ p.targetPlateau at hz
  rw [roundOverlapTransition_base, p.sourcePhaseToOverlap_base] at hz
  rw [p.sourcePhaseToOverlap_base]
  exact p.source_mem_halfBall_of_mapped_mem_targetPlateau z.1.property hz

private theorem roundOverlapTransition_mem_targetPhasePlateau (w : roundOverlap q d)
    (hw : (w.1.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)) :
    (roundOverlapTransition q d w).1 ∈ p.targetPhasePlateau := by
  change ((roundOverlapTransition q d w).1.1 : CoordinateSpace) ∈ p.targetPlateau
  rw [roundOverlapTransition_base]
  exact ⟨w.1.1, hw, rfl⟩

/-- Ambient source phase points in the source plateau with image in `S`
under the actual ambient round transition. -/
def sourcePhasePlateauPreimage (S : Set (Chart d.ball)) : Set (Chart q.ball) :=
  (Subtype.val : roundOverlap q d → Chart q.ball) ''
    {z | (z.1.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2) ∧
      (roundOverlapTransition q d z).1 ∈ S}

theorem sourcePhaseInclusion_image_preimage_targetPlateau
    (T : Chart p.sourceInput.ball → Chart p.targetInput.ball)
    (hComm : ∀ z, p.targetPhaseInclusion (T z) = (roundOverlapTransition q d (p.sourcePhaseToOverlap z)).1)
    (S : Set (Chart d.ball)) :
    p.sourcePhaseInclusion '' (T ⁻¹' (p.targetPhaseInclusion ⁻¹' (S ∩ p.targetPhasePlateau))) =
      p.sourcePhasePlateauPreimage S :=
  image_preimage_inter_of_lift T p.targetPhaseInclusion p.sourcePhaseToOverlap
    (fun z => (roundOverlapTransition q d z).1) Subtype.val S p.targetPhasePlateau
    {z | (z.1.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)}
    hComm p.sourcePhaseToOverlap_mem_halfBall
    (fun w hw => ⟨p.sourcePhaseToOverlap_mem_range w hw, p.roundOverlapTransition_mem_targetPhasePlateau w hw⟩)

end Burnett.Microlocal.OverlapWindows.CommonCutoffPatch
