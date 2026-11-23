import Burnett.Analysis.Microlocal.Overlap.CommonPatchPhaseInclusion
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryRay

/-!
# Round phase inclusions for a common cutoff patch

The same-chart ball inclusions preserve the Euclidean base coordinates and
unit covectors. As the preferred chart centers are fixed, the actual
inverse-transpose Jacobian and round normalization are the same before and
after these inclusions.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapWindows.CommonCutoffPatch

open Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors (roundOverlap roundOverlapDirection roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.FixedChartGeometricDensity (roundCovector)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

theorem sourcePhaseInclusion_mem_overlap
    (z : Chart (sourceInput (q := q) (d := d) p).ball) :
    sourcePhaseInclusion (q := q) (d := d) p z ∈ roundOverlap q d := by
  rcases z with ⟨⟨y, hy⟩, ξ⟩
  change y ∈ Metric.closedBall x p.sourceRadius at hy
  change y ∈ (chartTransition q.center d.center).source ∧
    chartTransition q.center d.center y ∈ d.ball.closedBall
  have hm : chartTransition q.center d.center y ∈ Metric.ball (chartTransition q.center d.center x) p.targetRadius :=
    p.mapsTo_targetBall hy
  exact ⟨(p.sourceWindow hy).1, interior_subset (p.targetWindow (Metric.ball_subset_closedBall hm)).2.1⟩

/-- Every small source phase point projects to the original pair's round overlap. -/
def sourcePhaseToOverlap (z : Chart (sourceInput (q := q) (d := d) p).ball) : roundOverlap q d :=
  ⟨sourcePhaseInclusion (q := q) (d := d) p z, sourcePhaseInclusion_mem_overlap (q := q) (d := d) p z⟩

theorem continuous_sourcePhaseToOverlap : Continuous (sourcePhaseToOverlap (q := q) (d := d) p) :=
  (continuous_sourcePhaseInclusion (q := q) (d := d) p).subtype_mk _

variable [IsManifold Model ∞ M]

theorem roundOverlapTransition_congr_coordinates {a b a' b' : CompactChartInput M}
    (hc : a'.center = a.center) (hd : b'.center = b.center)
    (u : roundOverlap a' b') (v : roundOverlap a b)
    (hx : (u.1.1 : CoordinateSpace) = v.1.1) (hξ : (u.1.2 : CoordinateSpace) = v.1.2) :
    ((roundOverlapTransition a' b' u).1.1 : CoordinateSpace) = (roundOverlapTransition a b v).1.1 ∧
    ((roundOverlapTransition a' b' u).1.2 : CoordinateSpace) = (roundOverlapTransition a b v).1.2 := by
  constructor
  · change chartTransition a'.center b'.center u.1.1 = chartTransition a.center b.center v.1.1
    rw [hc, hd, hx]
  · have hCovector : roundCovector u.1 = roundCovector v.1 := by
      funext i
      change (u.1.2 : CoordinateSpace) i = (v.1.2 : CoordinateSpace) i
      rw [hξ]
    have hDirection : roundOverlapDirection a' b' u = roundOverlapDirection a b v := by
      unfold roundOverlapDirection
      rw [hc, hd, hx, hCovector]
    change (‖roundOverlapDirection a' b' u‖⁻¹ : ℝ) • roundOverlapDirection a' b' u =
      (‖roundOverlapDirection a b v‖⁻¹ : ℝ) • roundOverlapDirection a b v
    rw [hDirection]

end Burnett.Microlocal.OverlapWindows.CommonCutoffPatch
