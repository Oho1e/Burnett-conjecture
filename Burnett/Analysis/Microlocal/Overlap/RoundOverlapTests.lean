import Burnett.Analysis.Microlocal.Overlap.AuxiliaryRay
import Burnett.Analysis.Microlocal.Overlap.MovingChartAngularSymbol

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.F05.OverlapCovectors
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.OverlapKernel
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- An actual homogeneous angular test is unchanged by round normalization
of the transported covector. -/
theorem movingChartAngularSymbol_eq_roundOverlap (q d : CompactChartInput M)
    (a m : E → ℂ) (hm : DegreeZero m) (p : roundOverlap q d) :
    movingChartAngularSymbol q.center d.center a m (p.1.1,p.1.2) =
      a p.1.1 * m (roundOverlapTransition q d p).1.2 := by
  have hF : frozenChartFrequency q.center d.center p.2.1 (p.1.2 : E) =
      roundOverlapDirection q d p := by
    apply WithLp.ofLp_injective 2
    exact frozenChartFrequency_cotangentCoords q.center d.center p.2.1 (p.1.2 : E)
  rw [movingChartAngularSymbol_eq_frozen q.center d.center a m p.2.1, hF]
  have hp : 0 < ‖roundOverlapDirection q d p‖ :=
    norm_pos_iff.mpr (roundOverlapDirection_ne_zero q d p)
  change a p.1.1 * m (roundOverlapDirection q d p) =
    a p.1.1 * m (‖roundOverlapDirection q d p‖⁻¹ • roundOverlapDirection q d p)
  rw [hm _ (inv_pos.mpr hp)]

/-- When the base tests also agree, the source moving symbol is exactly
the separated target symbol pulled back by the round overlap map. -/
theorem movingChartAngularSymbol_eq_targetRoundTest (q d : CompactChartInput M)
    (a b m : E → ℂ)
    (ha : ∀ x ∈ q.ball.closedBall, a x = b (chartTransition q.center d.center x))
    (hm : DegreeZero m) (p : roundOverlap q d) :
    movingChartAngularSymbol q.center d.center a m (p.1.1,p.1.2) =
      b (roundOverlapTransition q d p).1.1 * m (roundOverlapTransition q d p).1.2 := by
  rw [movingChartAngularSymbol_eq_roundOverlap q d a m hm p, ha _ p.1.1.property]
  rfl

end Burnett.Microlocal.Overlap
