import Burnett.Analysis.Microlocal.Overlap.CommonCutoffs
import Burnett.Analysis.Microlocal.CompactChartInput

/-!
# Actual chart inputs for a common cutoff patch

The smaller windows retain their ambient preferred chart centers. The
cutoffs, their transport, and their supports supply the hypotheses of the
matching-cutoff entry identity. The image of the closed inner source ball
is compact and contained in the interior of the full source-window image.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapWindows.CommonCutoffPatch

open Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

/-- Keep the preferred source chart and use the actual common source cutoff. -/
def sourceInput : CompactChartInput M where
  center := q.center
  ball := ⟨x, p.sourceRadius, p.sourceRadius_pos.le⟩
  ball_in_chart := fun _ hz => q.ball_in_chart (interior_subset (p.sourceWindow hz).2.1)
  cutoff := p.sourceCutoff
  cutoff_support := p.sourceCutoff_support.trans Metric.ball_subset_closedBall

/-- Keep the preferred target chart and use the actual transported cutoff. -/
def targetInput : CompactChartInput M where
  center := d.center
  ball := ⟨chartTransition q.center d.center x, p.targetRadius, p.targetRadius_pos.le⟩
  ball_in_chart := fun _ hy => d.ball_in_chart (interior_subset (p.targetWindow hy).2.1)
  cutoff := p.targetCutoff
  cutoff_support := p.targetCutoff_support.trans Metric.ball_subset_closedBall

theorem sourceInput_ball_subset_interior :
    p.sourceInput.ball.closedBall ⊆ interior q.ball.closedBall :=
  fun _ hz => (p.sourceWindow hz).2.1

theorem targetInput_ball_subset_interior :
    p.targetInput.ball.closedBall ⊆ interior d.ball.closedBall :=
  fun _ hy => (p.targetWindow hy).2.1

theorem sourceInput_ball_in_overlap :
    p.sourceInput.ball.closedBall ⊆ (chartTransition p.sourceInput.center p.targetInput.center).source :=
  fun _ hz => (p.sourceWindow hz).1

theorem sourceInput_mapsTo_targetInput :
    MapsTo (chartTransition p.sourceInput.center p.targetInput.center)
      p.sourceInput.ball.closedBall p.targetInput.ball.closedBall :=
  fun _ hz => Metric.ball_subset_closedBall (p.mapsTo_targetBall hz)

theorem targetInput_cutoff_support_image :
    tsupport (p.targetInput.cutoff : CoordinateSpace → ℝ) ⊆
      chartTransition p.sourceInput.center p.targetInput.center '' p.sourceInput.ball.closedBall :=
  p.targetCutoff_support_image.trans (image_mono p.sourceInput.cutoff_support)

theorem inputs_matching_cutoffs :
    ∀ z ∈ (chartTransition p.sourceInput.center p.targetInput.center).source,
      (p.targetInput.cutoff : CoordinateSpace → ℝ) (chartTransition p.sourceInput.center p.targetInput.center z) =
        (p.sourceInput.cutoff : CoordinateSpace → ℝ) z :=
  p.cutoff_transport

/-- The compact target plateau used to apply the unweighted local entry identity. -/
def targetPlateau : Set CoordinateSpace :=
  chartTransition p.sourceInput.center p.targetInput.center '' Metric.closedBall x (p.sourceRadius / 2)

private theorem halfBall_subset_sourceBall :
    Metric.closedBall x (p.sourceRadius / 2) ⊆ p.sourceInput.ball.closedBall :=
  Metric.closedBall_subset_closedBall (show p.sourceRadius / 2 ≤ p.sourceRadius by
    linarith [p.sourceRadius_pos])

theorem isCompact_targetPlateau : IsCompact p.targetPlateau :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartTransition p.sourceInput.center p.targetInput.center).continuousOn.mono
      (p.halfBall_subset_sourceBall.trans p.sourceInput_ball_in_overlap))

theorem targetPlateau_subset_interior_image : p.targetPlateau ⊆
    interior (chartTransition p.sourceInput.center p.targetInput.center '' p.sourceInput.ball.closedBall) := by
  let e := chartTransition p.sourceInput.center p.targetInput.center
  have hInner : Metric.closedBall x (p.sourceRadius / 2) ⊆ Metric.ball x p.sourceRadius :=
    Metric.closedBall_subset_ball (by linarith [p.sourceRadius_pos])
  have hOuter : Metric.ball x p.sourceRadius ⊆ p.sourceInput.ball.closedBall :=
    Metric.ball_subset_closedBall
  have hOpen : IsOpen (e '' Metric.ball x p.sourceRadius) :=
    e.isOpen_image_of_subset_source Metric.isOpen_ball (hOuter.trans p.sourceInput_ball_in_overlap)
  exact (image_mono hInner).trans (interior_maximal (image_mono hOuter) hOpen)

theorem targetPlateau_subset_targetBall : p.targetPlateau ⊆
    Metric.ball (chartTransition q.center d.center x) p.targetRadius := by
  rintro y ⟨z, hz, rfl⟩
  exact p.mapsTo_targetBall (p.halfBall_subset_sourceBall hz)

theorem targetInput_cutoff_one_on_targetPlateau :
    ∀ y ∈ p.targetPlateau, (p.targetInput.cutoff : CoordinateSpace → ℝ) y = 1 :=
  p.targetCutoff_one_on_image

end Burnett.Microlocal.OverlapWindows.CommonCutoffPatch
