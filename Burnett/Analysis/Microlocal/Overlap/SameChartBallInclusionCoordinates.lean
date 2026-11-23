import Burnett.Analysis.Microlocal.Overlap.SameChartBallInclusion

set_option autoImplicit false
set_option maxHeartbeats 105000

namespace Burnett.Microlocal.Overlap

open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.SmoothBaseTests (BallData)

theorem sameChartBallInclusion_fst {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall) (p : Chart L) :
    (sameChartBallInclusion hLK p).1 = Set.inclusion hLK p.1 := by
  rcases p with ⟨x, ξ⟩
  rfl

theorem sameChartBallInclusion_snd {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall) (p : Chart L) :
    (sameChartBallInclusion hLK p).2 = p.2 := by
  rcases p with ⟨⟨x, hx⟩, ξ⟩
  rfl

end Burnett.Microlocal.Overlap
