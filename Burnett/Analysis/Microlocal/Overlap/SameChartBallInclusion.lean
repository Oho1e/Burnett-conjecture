import Burnett.Analysis.Microlocal.CompactJetMatrixMeasure

set_option autoImplicit false

namespace Burnett.Microlocal.Overlap

open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.SmoothBaseTests (BallData)

/-- The inclusion of nested compact balls preserves both ambient phase
coordinates in a single preferred chart. -/
def sameChartBallInclusion {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall) (p : Chart L) : Chart K :=
  (⟨p.1, hLK p.1.property⟩, p.2)

theorem continuous_sameChartBallInclusion {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall) :
    Continuous (sameChartBallInclusion hLK) :=
  ((continuous_subtype_val.comp continuous_fst).subtype_mk _).prodMk continuous_snd

end Burnett.Microlocal.Overlap
