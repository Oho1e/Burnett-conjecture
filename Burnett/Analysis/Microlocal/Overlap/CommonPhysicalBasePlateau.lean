import Burnett.Analysis.Microlocal.Overlap.NormalizedEntryTransport

/-! A common cutoff plateau as one subset of the actual cotangent bundle. -/

set_option autoImplicit false
set_option maxHeartbeats 170000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition (chartTransition_symm_point)
open Burnett.Geometry.UnitNullCompactness (CotangentBundle continuous_cotangent_projection)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay)
open Burnett.F05.OverlapCovectors (roundOverlap)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.OverlapWindows (CommonCutoffPatch)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

omit [IsManifold Model ∞ M] in
private theorem halfBall_subset_window : Metric.closedBall x (p.sourceRadius / 2) ⊆
    Metric.closedBall x p.sourceRadius :=
  Metric.closedBall_subset_closedBall (by linarith [p.sourceRadius_pos])

omit [IsManifold Model ∞ M] in
private theorem sourcePlateau_in_chart : Metric.closedBall x (p.sourceRadius / 2) ⊆
    (chartAt CoordinateSpace q.center).target :=
  fun _ hz => q.ball_in_chart (interior_subset (p.sourceWindow (halfBall_subset_window p hz)).2.1)

/-- The actual base plateau, defined in the original source chart. -/
def commonPatchBasePlateau : Set M :=
  (chartAt CoordinateSpace q.center).symm '' Metric.closedBall x (p.sourceRadius / 2)

omit [IsManifold Model ∞ M] in
theorem isCompact_commonPatchBasePlateau : IsCompact (commonPatchBasePlateau p) :=
  (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt CoordinateSpace q.center).continuousOn_symm.mono (sourcePlateau_in_chart p))

omit [IsManifold Model ∞ M] in
theorem commonPatchBasePlateau_target_image :
    commonPatchBasePlateau p = (chartAt CoordinateSpace d.center).symm '' p.targetPlateau := by
  change (chartAt CoordinateSpace q.center).symm '' Metric.closedBall x (p.sourceRadius / 2) =
    (chartAt CoordinateSpace d.center).symm ''
      (chartTransition q.center d.center '' Metric.closedBall x (p.sourceRadius / 2))
  rw [image_image]
  apply image_congr
  intro y hy
  exact (chartTransition_symm_point q.center d.center (p.sourceWindow (halfBall_subset_window p hy)).1).symm

/-- The two chart windows pull back the cotangent plateau to their respective
source and target phase plateaus. -/
def commonPatchCotangentPlateau : Set (CotangentBundle M) :=
  (fun z => z.proj) ⁻¹' commonPatchBasePlateau p

theorem measurableSet_commonPatchCotangentPlateau [T2Space M] [MeasurableSpace (CotangentBundle M)]
    [BorelSpace (CotangentBundle M)] : MeasurableSet (commonPatchCotangentPlateau p) :=
  ((isCompact_commonPatchBasePlateau p).isClosed.preimage continuous_cotangent_projection).measurableSet

private theorem chartAuxiliaryRay_base (r : Metric (M := M))
    (a : CompactChartInput M) (z : Chart a.ball) :
    (chartAuxiliaryRay r a z).proj = (chartAt CoordinateSpace a.center).symm z.1 :=
  rfl

theorem chartAuxiliaryRay_preimage_source_commonPatchPlateau (r : Metric (M := M)) :
    chartAuxiliaryRay r q ⁻¹' commonPatchCotangentPlateau p =
      {z : Chart q.ball | (z.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)} := by
  ext z
  change (chartAuxiliaryRay r q z).proj ∈ commonPatchBasePlateau p ↔ _
  rw [chartAuxiliaryRay_base, commonPatchBasePlateau]
  let e := chartAt CoordinateSpace q.center
  constructor
  · rintro ⟨y, hy, he⟩
    have heq : y = (z.1 : CoordinateSpace) :=
      e.symm.injOn (sourcePlateau_in_chart p hy) (q.ball_in_chart z.1.property) he
    change (z.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)
    exact heq ▸ hy
  · exact fun hz => mem_image_of_mem e.symm hz

theorem chartAuxiliaryRay_preimage_target_commonPatchPlateau (r : Metric (M := M)) :
    chartAuxiliaryRay r d ⁻¹' commonPatchCotangentPlateau p = p.targetPhasePlateau := by
  ext z
  change (chartAuxiliaryRay r d z).proj ∈ commonPatchBasePlateau p ↔ _
  rw [chartAuxiliaryRay_base, commonPatchBasePlateau_target_image]
  let e := chartAt CoordinateSpace d.center
  constructor
  · rintro ⟨y, hy, he⟩
    have hBall := Metric.ball_subset_closedBall (p.targetPlateau_subset_targetBall hy)
    have hy' : y ∈ e.target := d.ball_in_chart (p.targetInput_ball_subset_interior.trans interior_subset hBall)
    have heq : y = (z.1 : CoordinateSpace) := e.symm.injOn hy' (d.ball_in_chart z.1.property) he
    change (z.1 : CoordinateSpace) ∈ p.targetPlateau
    exact heq ▸ hy
  · exact fun hz => mem_image_of_mem e.symm hz

omit [IsManifold Model ∞ M] in
theorem sourcePlateau_subset_roundOverlap :
    {z : Chart q.ball | (z.1 : CoordinateSpace) ∈ Metric.closedBall x (p.sourceRadius / 2)}
      ⊆ roundOverlap q d := by
  intro z hz
  have h := p.sourceWindow_subset_nonzeroCutoffOverlap (halfBall_subset_window p hz)
  exact ⟨h.1.1, interior_subset h.1.2.1⟩

end Burnett.Microlocal.Overlap
