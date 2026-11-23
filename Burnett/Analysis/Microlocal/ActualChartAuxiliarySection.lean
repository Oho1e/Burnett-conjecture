import Burnett.Analysis.Microlocal.AuxiliaryCovectorScale
import Burnett.Analysis.Microlocal.CompactChartInput
import Burnett.Analysis.Microlocal.RoundChartCovariance
import Burnett.Geometry.Cotangent.Core

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.ActualChartAuxiliarySection

open Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference ManifoldMetric UnitNullCompactness
open Burnett.Geometry.InverseField (matrixInverse continuousOn_matrixInverse)
open Burnett.Microlocal.SmoothBaseTests Burnett.Microlocal.SmoothAngularTests
open Burnett.Microlocal.CountableAuxiliaryCharts Burnett.Microlocal.FixedChartGeometricDensity
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Restriction of the inverse auxiliary metric in the prescribed preferred chart. -/
def chartAuxiliaryInverse (r : ManifoldMetric.Metric (M := M)) (q : CompactChartInput M)
    (y : q.ball.Point) : Tensor2 :=
  matrixInverse (metricComponents (coordinateMetric r q.center) y)

theorem continuous_chartAuxiliaryInverse (r : ManifoldMetric.Metric (M := M))
    (q : CompactChartInput M) :
    Continuous (chartAuxiliaryInverse r q) := by
  have h : ContinuousOn (fun y => matrixInverse (metricComponents (coordinateMetric r q.center) y))
      (chartAt CoordinateSpace q.center).target :=
    continuousOn_matrixInverse _ _ (continuousOn_pi.mpr fun a => continuousOn_pi.mpr fun b =>
      (contDiffOn_metricComponents r q.center a b).continuousOn)
      (fun _ hyt => (coordinateMetric_posDef r q.center hyt).det_pos.ne')
  exact continuousOn_iff_continuous_restrict.mp (h.mono q.ball_in_chart)

theorem chartAuxiliaryNorm_pos (r : ManifoldMetric.Metric (M := M)) (q : CompactChartInput M)
    (p : Chart q.ball) : 0 < symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p) := by
  have hξ : roundCovector p ≠ 0 := by
    intro heq
    simpa only [heq, Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_ne_one] using
      roundCovector_dual_pairing p
  have hpd : Matrix.PosDef (chartAuxiliaryInverse r q p.1) :=
    (coordinateMetric_posDef r q.center (q.ball_in_chart p.1.property)).inv
  rw [symbolNorm_eq_gramEnergy, GramCoordinateBound.gramEnergy]
  simpa only [star_trivial] using hpd.2 _ hξ

/-- The radial image as an actual element of the cotangent bundle. -/
def chartAuxiliaryRay (r : ManifoldMetric.Metric (M := M)) (q : CompactChartInput M)
    (p : Chart q.ball) : CotangentBundle M :=
  cotangentAssemble q.center
    ((chartAt CoordinateSpace q.center).symm p.1,
      auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p))

theorem continuous_chartAuxiliaryRay (r : ManifoldMetric.Metric (M := M))
    (q : CompactChartInput M) : Continuous (chartAuxiliaryRay r q) := by
  let e := chartAt CoordinateSpace q.center
  have hn : Continuous (fun p : Chart q.ball =>
      symbolNorm (chartAuxiliaryInverse r q p.1) (roundCovector p)) := by
    have hξ (a : Index) : Continuous (fun p : Chart q.ball => roundCovector p a) :=
      ((sphereCoordinate a).continuous.comp continuous_snd).congr
        (fun p => sphereCoordinate_apply a p.2)
    exact continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ =>
      ((((continuous_apply b).comp (continuous_apply a)).comp
        ((continuous_chartAuxiliaryInverse r q).comp continuous_fst)).mul (hξ a)).mul (hξ b)
  have haux : Continuous (fun p : Chart q.ball =>
      auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)) := by
    apply continuous_pi
    intro a
    have hξ : Continuous (fun p : Chart q.ball => roundCovector p a) :=
      ((sphereCoordinate a).continuous.comp continuous_snd).congr
        (fun p => sphereCoordinate_apply a p.2)
    exact ((Real.continuous_sqrt.comp hn).inv₀ (fun p =>
      (Real.sqrt_pos.mpr (chartAuxiliaryNorm_pos r q p)).ne')).mul hξ
  have hb : Continuous (fun p : Chart q.ball => e.symm p.1) :=
    (continuousOn_iff_continuous_restrict.mp (e.continuousOn_symm.mono q.ball_in_chart)).comp
      continuous_fst
  exact continuousOn_univ.mp ((continuousOn_cotangentAssemble q.center).comp
    (hb.prodMk haux).continuousOn (fun p _ => e.symm_mapsTo (q.ball_in_chart p.1.property)))

theorem chartAuxiliaryRay_coords (r : ManifoldMetric.Metric (M := M))
    (q : CompactChartInput M) (p : Chart q.ball) :
    cotangentCoords q.center (chartAuxiliaryRay r q p) =
      auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p) :=
  cotangentCoords_assemble _ _ ((chartAt CoordinateSpace q.center).symm_mapsTo
    (q.ball_in_chart p.1.property))

theorem chartAuxiliaryRay_unit (r : ManifoldMetric.Metric (M := M))
    (q : CompactChartInput M) (p : Chart q.ball) :
    dualEnergy r.inner (GlobalLeviCivita.inner_nondegenerate r) (chartAuxiliaryRay r q p) = 1 := by
  have ht := q.ball_in_chart p.1.property
  rw [dualEnergy_chart r.inner (GlobalLeviCivita.inner_nondegenerate r) r.symm q.center
    (chartAuxiliaryRay r q p) ((chartAt CoordinateSpace q.center).symm_mapsTo ht),
    chartAuxiliaryRay_coords]
  change symbolNorm (matrixInverse (metricComponents (coordinateMetric r q.center)
    (chartAt CoordinateSpace q.center ((chartAt CoordinateSpace q.center).symm p.1))))
    (auxiliaryUnitCovector (chartAuxiliaryInverse r q p.1) (roundCovector p)) = 1
  rw [(chartAt CoordinateSpace q.center).right_inv ht]
  exact auxiliaryUnitCovector_unit _ _ (chartAuxiliaryNorm_pos r q p)

end Burnett.F05.ActualChartAuxiliarySection
