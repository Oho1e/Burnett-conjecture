import Burnett.Analysis.Microlocal.ActualChartAuxiliarySection
import Burnett.Geometry.Cotangent.CosphereMeasure

set_option autoImplicit false

noncomputable section
namespace Burnett.F05.ActualChartAuxiliarySection

open Set MeasureTheory Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.FixedChartGeometricDensity
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The auxiliary normalization retains the base and the oriented round ray. -/
theorem injective_chartAuxiliaryRay (r : Metric (M := M)) (q : CompactChartInput M) :
    Function.Injective (chartAuxiliaryRay r q) := by
  intro z y h
  let e := chartAt CoordinateSpace q.center
  have hbase := congrArg (fun p : CotangentBundle M => e p.proj) h
  change e (e.symm z.1) = e (e.symm y.1) at hbase
  rw [e.right_inv (q.ball_in_chart z.1.property), e.right_inv (q.ball_in_chart y.1.property)] at hbase
  have hcoords := congrArg (cotangentCoords q.center) h
  rw [chartAuxiliaryRay_coords, chartAuxiliaryRay_coords] at hcoords
  let a (p : Chart q.ball) := auxiliaryScale (chartAuxiliaryInverse r q p.1) (roundCovector p)
  have hScalePos (p : Chart q.ball) : 0 < a p :=
    auxiliaryScale_pos _ _ (chartAuxiliaryNorm_pos r q p)
  have hsum (p : Chart q.ball) :
      (∑ i, (a p * roundCovector p i) * (a p * roundCovector p i)) = (a p)^2 := by
    calc
      _ = (a p)^2 * ∑ i, roundCovector p i * roundCovector p i := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by rw [roundCovector_dual_pairing, mul_one]
  change (fun i => a z * roundCovector z i) = (fun i => a y * roundCovector y i) at hcoords
  have hscale : a z = a y := by
    apply (sq_eq_sq₀ (hScalePos z).le (hScalePos y).le).mp
    rw [← hsum z, ← hsum y]
    exact congrArg (fun v : Covector => ∑ i, v i * v i) hcoords
  refine Prod.ext (Subtype.ext hbase) (Subtype.ext (PiLp.ext fun i => ?_))
  have hi := congrFun hcoords i
  change a z * roundCovector z i = a y * roundCovector y i at hi
  rw [hscale] at hi
  exact mul_left_cancel₀ (hScalePos y).ne' hi

/-- A round chart point as a point of the actual full unit section. -/
def chartAuxiliaryCosphere (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) : Cosphere r :=
  ⟨chartAuxiliaryRay r q z, chartAuxiliaryRay_unit r q z⟩

theorem continuous_chartAuxiliaryCosphere (r : Metric (M := M)) (q : CompactChartInput M) :
    Continuous (chartAuxiliaryCosphere r q) :=
  (continuous_chartAuxiliaryRay r q).subtype_mk _

theorem measurableEmbedding_chartAuxiliaryCosphere [T2Space M]
    (r : Metric (M := M)) (q : CompactChartInput M) :
    MeasurableEmbedding (chartAuxiliaryCosphere r q) := by
  letI : T2Space (CotangentBundle M) := CotangentAngularExtension.cotangentBundle_t2Space
  exact ((continuous_chartAuxiliaryCosphere r q).isClosedEmbedding
    (fun _ _ h => injective_chartAuxiliaryRay r q (congrArg Subtype.val h))).measurableEmbedding

end Burnett.F05.ActualChartAuxiliarySection
