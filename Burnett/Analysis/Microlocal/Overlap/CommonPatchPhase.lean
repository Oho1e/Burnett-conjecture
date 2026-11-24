import Burnett.Analysis.Microlocal.Overlap.CommonPatchAmbientOverlap
import Burnett.Analysis.Microlocal.Overlap.OverlapWeightedEntryMeasures

/-! The round chart-window map commutes with the inclusions into the ambient overlap. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapWindows.CommonCutoffPatch

open Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors (roundOverlap roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.Overlap (roundChartWindowMap)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

section RoundTransition

variable [IsManifold Model ∞ M]

private theorem roundChartWindowMap_val (a b : CompactChartInput M)
    (hs : a.ball.closedBall ⊆ (chartTransition a.center b.center).source)
    (ht : MapsTo (chartTransition a.center b.center) a.ball.closedBall b.ball.closedBall)
    (z : Chart a.ball) :
    roundChartWindowMap a b hs ht z = (roundOverlapTransition a b ⟨z, hs z.1.property, ht z.1.property⟩).1 :=
  rfl

private theorem roundOverlapTransition_inclusion_of_coordinates {a b a' b' : CompactChartInput M}
    (hc : a'.center = a.center) (hd : b'.center = b.center)
    (u : roundOverlap a' b') (v : roundOverlap a b)
    (hx : (u.1.1 : CoordinateSpace) = v.1.1) (hξ : (u.1.2 : CoordinateSpace) = v.1.2)
    (incl : Chart b'.ball → Chart b.ball)
    (hBase : ∀ z, ((incl z).1 : CoordinateSpace) = z.1)
    (hDir : ∀ z, ((incl z).2 : CoordinateSpace) = z.2) :
    incl (roundOverlapTransition a' b' u).1 = (roundOverlapTransition a b v).1 := by
  have h := roundOverlapTransition_congr_coordinates hc hd u v hx hξ
  exact Prod.ext (Subtype.ext ((hBase _).trans h.1)) (Subtype.ext ((hDir _).trans h.2))

end RoundTransition

variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

private theorem sourcePhaseInclusion_base
    (z : Chart (sourceInput (q := q) (d := d) p).ball) :
    Subtype.val (sourcePhaseInclusion (q := q) (d := d) p z).1 = Subtype.val z.1 := by
  rcases z with ⟨⟨y, hy⟩, ξ⟩
  change y = y
  rfl

private theorem targetPhaseInclusion_base
    (z : Chart (targetInput (q := q) (d := d) p).ball) :
    Subtype.val (targetPhaseInclusion (q := q) (d := d) p z).1 = Subtype.val z.1 := by
  rcases z with ⟨⟨y, hy⟩, ξ⟩
  change y = y
  rfl

private theorem sourcePhaseInclusion_direction
    (z : Chart (sourceInput (q := q) (d := d) p).ball) :
    Subtype.val (sourcePhaseInclusion (q := q) (d := d) p z).2 = Subtype.val z.2 := by
  rcases z with ⟨⟨y, hy⟩, ξ⟩
  rfl

private theorem targetPhaseInclusion_direction
    (z : Chart (targetInput (q := q) (d := d) p).ball) :
    Subtype.val (targetPhaseInclusion (q := q) (d := d) p z).2 = Subtype.val z.2 := by
  rcases z with ⟨⟨y, hy⟩, ξ⟩
  rfl

variable [IsManifold Model ∞ M]

/-- The small-window map of the entry identity is exactly the restriction of
the ambient overlap transition, after inclusion in the ambient target window. -/
theorem roundChartWindowMap_inclusion
    (z : Chart (sourceInput (q := q) (d := d) p).ball) :
    targetPhaseInclusion (q := q) (d := d) p
      (roundChartWindowMap (sourceInput (q := q) (d := d) p) (targetInput (q := q) (d := d) p)
        (sourceInput_ball_in_overlap (q := q) (d := d) p) (sourceInput_mapsTo_targetInput (q := q) (d := d) p) z) =
    (roundOverlapTransition q d (sourcePhaseToOverlap (q := q) (d := d) p z)).1 := by
  let a := sourceInput (q := q) (d := d) p
  let b := targetInput (q := q) (d := d) p
  let hs := sourceInput_ball_in_overlap (q := q) (d := d) p
  let ht := sourceInput_mapsTo_targetInput (q := q) (d := d) p
  let u : roundOverlap a b := ⟨z, hs z.1.property, ht z.1.property⟩
  let v : roundOverlap q d := sourcePhaseToOverlap (q := q) (d := d) p z
  let incl := targetPhaseInclusion (q := q) (d := d) p
  have hBase : (u.1.1 : CoordinateSpace) = v.1.1 := (sourcePhaseInclusion_base (q := q) (d := d) p z).symm
  have hDir : (u.1.2 : CoordinateSpace) = v.1.2 := (sourcePhaseInclusion_direction (q := q) (d := d) p z).symm
  have h := roundOverlapTransition_inclusion_of_coordinates (a := q) (b := d) (a' := a) (b' := b)
    rfl rfl u v hBase hDir incl (targetPhaseInclusion_base (q := q) (d := d) p)
      (targetPhaseInclusion_direction (q := q) (d := d) p)
  exact (congrArg incl (roundChartWindowMap_val a b hs ht z)).trans h

end Burnett.Microlocal.OverlapWindows.CommonCutoffPatch
