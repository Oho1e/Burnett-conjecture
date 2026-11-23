import Burnett.Analysis.Microlocal.Overlap.SameChartBallInclusion
import Burnett.Analysis.Microlocal.CompactChartInput
import Burnett.Analysis.Microlocal.RationalAngularDensity

set_option autoImplicit false

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.SmoothBaseTests (BallData)

/-- Inclusion of nested compact phase windows preserves Borel sets in both
directions between the smaller window and its image. -/
theorem measurableEmbedding_sameChartBallInclusion
    {L K : BallData} (hLK : L.closedBall ⊆ K.closedBall) :
    MeasurableEmbedding (sameChartBallInclusion hLK) := by
  let f : L.Point → K.Point := Subtype.map id (fun _ hz => hLK hz)
  have hf : Function.Injective f := Subtype.map_injective _ Function.injective_id
  have hi : Function.Injective (sameChartBallInclusion hLK) := hf.prodMap Function.injective_id
  exact ((continuous_sameChartBallInclusion hLK).isClosedEmbedding hi).measurableEmbedding

end Burnett.Microlocal.Overlap
