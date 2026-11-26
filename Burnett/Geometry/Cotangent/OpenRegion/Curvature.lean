import Burnett.Geometry.Cotangent.OpenRegion.Metrics
import Burnett.Counterexamples.Bianchi.Geometry
import Burnett.Geometry.IntrinsicScalarEinstein

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter Bundle
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ContravariantTensor Burnett.Geometry.IntrinsicScalarEinstein
open Burnett.Geometry.CurvatureDifference (coordinateRicci)
open Burnett.Geometry.BackgroundConnection (computedConnection)

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

theorem chartEinstein_openSubtype (U : Opens M) (g : Field (M := M))
    (c : U) {y : E} (hy : y ∈ (chartAt E c).target) :
    chartEinstein (restrictBilinear U g) c y = chartEinstein g c.val y := by
  let A := coordinateBilinear (restrictBilinear U g) c
  let B := coordinateBilinear g c.val
  have hNear : A =ᶠ[𝓝 y] B := Filter.eventuallyEq_of_mem
    ((chartAt E c).open_target.mem_nhds hy) (fun _ hz => coordinateBilinear_openSubtype U g c hz)
  have hRicci : coordinateRicci (computedConnection A) y = coordinateRicci (computedConnection B) y :=
    Burnett.Bianchi.coordinateRicci_congr_germ _ _ y (Burnett.Bianchi.computedConnection_congr_germ _ _ y hNear)
  have hMetric : metricComponents A y = metricComponents B y :=
    congrArg (fun F : LinearMap.BilinForm ℝ E => FiberMetric.covariant F coordinateBasis) hNear.self_of_nhds
  have hScalar : chartScalarCurvature (restrictBilinear U g) c y = chartScalarCurvature g c.val y := by
    change Burnett.RicciSymbol.metricTrace (InverseField.matrixInverse (metricComponents A y))
      (coordinateRicci (computedConnection A) y) = Burnett.RicciSymbol.metricTrace
      (InverseField.matrixInverse (metricComponents B y)) (coordinateRicci (computedConnection B) y)
    rw [hMetric, hRicci]
  change (fun i j => coordinateRicci (computedConnection A) y i j -
      (chartScalarCurvature (restrictBilinear U g) c y / 2) * metricComponents A y i j) =
    (fun i j => coordinateRicci (computedConnection B) y i j -
      (chartScalarCurvature g c.val y / 2) * metricComponents B y i j)
  rw [hScalar, hRicci, hMetric]

/-- Locality of the Einstein tensor along the actual inclusion of an open set. -/
theorem intrinsicEinstein_openSubtype [T2Space M] (U : Opens M) (g : Field (M := M))
    (hg : IsSmooth g) (hn : IsNondegenerate g) (hs : IsSymmetric g) (x : U) :
    intrinsicEinstein (restrictBilinear U g) (fun x => hn x.val) x = intrinsicEinstein g hn x.val := by
  have hx : x ∈ (chartAt E x).source := mem_chart_source E x
  have hxM : x.val ∈ (chartAt E x.val).source := hx.2
  let b := tensorTangentBasis x x hx
  have hBasis (i) : b i = tensorTangentBasis x.val x.val hxM i := by
    rw [tensorTangentBasis_apply, tensorTangentBasis_apply, tangentFrame_openSubtype U x x hx]
    rfl
  apply b.ext
  intro i
  apply b.ext
  intro j
  change intrinsicEinstein (restrictBilinear U g) (fun x => hn x.val) x (b i) (b j) =
    intrinsicEinstein g hn x.val (b i) (b j)
  rw [show intrinsicEinstein (restrictBilinear U g) (fun x => hn x.val) x (b i) (b j) = _ from
    intrinsicEinstein_components (restrictBilinear U g) (isSmooth_restrictBilinear U g hg)
      (fun x => hs x.val) (fun x => hn x.val) x x hx i j,
    hBasis i, hBasis j, intrinsicEinstein_components g hg hs hn x.val x.val hxM i j]
  change chartEinstein (restrictBilinear U g) x (chartAt E x x) i j = chartEinstein g x.val (chartAt E x x) i j
  rw [chartEinstein_openSubtype U g x ((chartAt E x).mapsTo hx)]

end Burnett.Geometry.OpenRegion
