import Burnett.Analysis.Microlocal.Overlap.CommonPatchInputs
import Burnett.Analysis.Microlocal.Overlap.SameChartBallInclusion

/-! The small windows include into their respective ambient round phase spaces. -/

set_option autoImplicit false

namespace Burnett.Microlocal.OverlapWindows.CommonCutoffPatch

open Set
open Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.Overlap (sameChartBallInclusion continuous_sameChartBallInclusion)
open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

def sourcePhaseInclusion : Chart p.sourceInput.ball → Chart q.ball :=
  sameChartBallInclusion (p.sourceInput_ball_subset_interior.trans interior_subset)

def targetPhaseInclusion : Chart p.targetInput.ball → Chart d.ball :=
  sameChartBallInclusion (p.targetInput_ball_subset_interior.trans interior_subset)

theorem continuous_sourcePhaseInclusion : Continuous p.sourcePhaseInclusion :=
  continuous_sameChartBallInclusion _

theorem continuous_targetPhaseInclusion : Continuous p.targetPhaseInclusion :=
  continuous_sameChartBallInclusion _

end Burnett.Microlocal.OverlapWindows.CommonCutoffPatch
