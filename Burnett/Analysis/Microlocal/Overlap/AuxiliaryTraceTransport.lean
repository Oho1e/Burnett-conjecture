import Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeContractions
import Burnett.Analysis.Microlocal.Overlap.AmplitudeEntryRecovery
import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeCoordinates

/-! Auxiliary trace comparison in the two actual ordered coordinate representations. -/

set_option autoImplicit false
set_option maxHeartbeats 750000

noncomputable section

namespace Burnett.F07.IntrinsicAmplitude

open Module Matrix Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Geometry.ContravariantTensor (tensorTangentBasis tensorTangentBasis_apply)
open Burnett.Geometry.ManifoldMetricTransition (chartTransition_symm_point)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryInverse)
open Burnett.F05.OverlapCovectors (roundOverlap roundOverlapTransition tensorPairTransition)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeFiber chartTangentBasis chartTangentBasis_preferred chartComponents components_apply
    chartAmplitude chartComponents_chartAmplitude chartAmplitude_change
    fixedCotangentTransitionMatrix fixedCotangentTransitionMatrix_preferred)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.Microlocal.Overlap (receivingToSourceCotangent receivingToSourceCotangent_actual)
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem auxiliaryTraceInBasis_preferred (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) (x : M) (hx : x ∈ (chartAt CoordinateSpace q.center).source)
    (hbase : x = (chartAt CoordinateSpace q.center).symm z.1) (F : AmplitudeFiber x) :
    auxiliaryTraceInBasis (chartTangentBasis (.atPoint q.center) x hx)
      (inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x) F =
      auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1)
        (chartComponents (.atPoint q.center) x hx F) := by
  subst x
  let x := (chartAt CoordinateSpace q.center).symm z.1
  let b := chartTangentBasis (.atPoint q.center) x hx
  have hb : b = chartAmplitudeTangentBasis r q z := by
    apply Basis.eq_of_apply_eq
    intro i
    change chartTangentBasis (.atPoint q.center) x hx i = _
    rw [chartTangentBasis_preferred]
    change tangentFrame q.center x (coordinateBasis i) = tensorTangentBasis q.center x hx i
    exact (tensorTangentBasis_apply q.center x hx i).symm
  have hR : (fun i j => inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x
      (b.dualBasis i) (b.dualBasis j) : Tensor2) = chartAuxiliaryInverse r q z.1 := by
    rw [hb]
    ext i j
    exact chartAuxiliaryInverse_eq_fiber_entries r q z i j
  change auxiliaryTraceInBasis b _ F = _
  rw [auxiliaryTraceInBasis, hR, chartComponents]
  congr 1
  ext i j
  exact (components_apply b F i j).symm

/-- The two genuine auxiliary inverses give the same real trace after the
ordered amplitude matrix is transported from the receiving chart to the source chart. -/
theorem auxiliaryTraceLinear_roundOverlap (r : Metric (M := M)) (q d : CompactChartInput M)
    (z : roundOverlap d q) (A : Matrix Pair Pair ℂ) :
    let D := tensorPairTransition (receivingToSourceCotangent q d z.1.1)
    auxiliaryTraceLinear (chartAuxiliaryInverse r q (roundOverlapTransition d q z).1.1) (D * A * Dᴴ) =
      auxiliaryTraceLinear (chartAuxiliaryInverse r d z.1.1) A := by
  intro D
  let x := (chartAt CoordinateSpace d.center).symm z.1.1
  let zq := (roundOverlapTransition d q z).1
  have hbase : (chartAt CoordinateSpace q.center).symm zq.1 = x :=
    chartTransition_symm_point d.center q.center z.2.1
  have hxq : x ∈ (chartAt CoordinateSpace q.center).source := by
    rw [← hbase]
    exact (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart zq.1.property)
  have hxd : x ∈ (chartAt CoordinateSpace d.center).source :=
    (chartAt CoordinateSpace d.center).symm_mapsTo (d.ball_in_chart z.1.1.property)
  let cq : AtlasChart M := .atPoint q.center
  let cd : AtlasChart M := .atPoint d.center
  let Q := inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x
  let Aq := chartAmplitude cq x hxq (D * A * Dᴴ)
  let Ad := chartAmplitude cd x hxd A
  have hD : D = tensorPairTransition (fixedCotangentTransitionMatrix cd cq x) := by
    dsimp only [D, cd, cq, x]
    rw [fixedCotangentTransitionMatrix_preferred, receivingToSourceCotangent_actual]
  have hAmplitude : Aq = Ad := by
    change chartAmplitude cq x hxq (D * A * Dᴴ) = chartAmplitude cd x hxd A
    rw [hD]
    exact chartAmplitude_change cd cq x hxd hxq A
  calc
    auxiliaryTraceLinear (chartAuxiliaryInverse r q zq.1) (D * A * Dᴴ) =
        auxiliaryTraceInBasis (chartTangentBasis cq x hxq) Q Aq := by
      rw [auxiliaryTraceInBasis_preferred r q zq x hxq hbase.symm]
      change _ = auxiliaryTraceLinear _ (chartComponents cq x hxq Aq)
      rw [show Aq = chartAmplitude cq x hxq (D * A * Dᴴ) by rfl, chartComponents_chartAmplitude]
    _ = auxiliaryTraceInBasis (chartTangentBasis cd x hxd) Q Ad := by
      rw [hAmplitude, auxiliaryTraceInBasis_eq]
    _ = auxiliaryTraceLinear (chartAuxiliaryInverse r d z.1.1) A := by
      rw [auxiliaryTraceInBasis_preferred r d z.1 x hxd rfl]
      change auxiliaryTraceLinear _ (chartComponents cd x hxd Ad) = _
      rw [show Ad = chartAmplitude cd x hxd A by rfl, chartComponents_chartAmplitude]

end Burnett.F07.IntrinsicAmplitude
