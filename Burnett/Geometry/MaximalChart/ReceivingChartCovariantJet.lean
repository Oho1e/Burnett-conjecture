import Burnett.Geometry.MaximalChart.CurvatureTransfer
import Burnett.Geometry.IntrinsicDhMeasure
import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeCoordinates

/-! The covariant derivative of an intrinsic bilinear field in a maximal-atlas chart. -/

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Filter Set Burnett.RicciSymbol
open Burnett.Geometry BackgroundConnection ConnectionDifference ManifoldMetric ManifoldBilinear ChartVolume
  ManifoldMetricTransition
open Burnett.Geometry.FixedCotangentChart (inverseFrame inverseFrame_change)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis chartTangentBasis_apply inverseFrame_preferred)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The coordinate array formed from the actual Christoffel symbols and the
actual first derivative of a bilinear field. -/
def fixedCovariantJet (R H : Field (M := M)) (c : AtlasChart M) (x : CoordinateSpace) : FirstJet :=
  covariantJet (computedConnection (fixedForm R c) x)
    (metricComponents (fixedForm H c) x) (coordinateJet (metricComponents (fixedForm H c)) x)

private theorem fixedForm_coordinateJet_eq_preferred (H : Field (M := M)) (q : M)
    {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace q).target) :
    coordinateJet (metricComponents (fixedForm H (.atPoint q))) x =
      coordinateJet (metricComponents (coordinateBilinear H q)) x := by
  funext b i j
  have he : (fun y => metricComponents (fixedForm H (.atPoint q)) y i j) =ᶠ[𝓝 x]
      (fun y => metricComponents (coordinateBilinear H q) y i j) := by
    filter_upwards [(chartAt CoordinateSpace q).open_target.mem_nhds hx] with y hy
    rw [fixedForm_eq_preferred_components H q hy]
  exact congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (EuclideanSpace.single b 1)) he.fderiv_eq

theorem fixedCovariantJet_eq_preferred (r : Metric (M := M)) (H : Field (M := M)) (q : M)
    {x : CoordinateSpace} (hx : x ∈ (chartAt CoordinateSpace q).target) :
    fixedCovariantJet r.inner H (.atPoint q) x = IntrinsicDhMeasure.coordinateDerivativeTensor r H q x := by
  unfold fixedCovariantJet IntrinsicDhMeasure.coordinateDerivativeTensor computedConnection
  rw [fixedForm_eq_preferred_components r.inner q hx, fixedForm_eq_preferred_components H q hx,
    fixedForm_coordinateJet_eq_preferred r.inner q hx, fixedForm_coordinateJet_eq_preferred H q hx]
  rfl

variable [SecondCountableTopology M]

/-- All three covariant indices transform by the actual first derivative of
the chart transition. The Hessian terms cancel with the connection change. -/
theorem fixedCovariantJet_change (R H : Field (M := M))
    (hR : IsSmooth R) (hs : IsSymmetric R) (hn : IsNondegenerate R) (hH : IsSmooth H)
    (c d : AtlasChart M) (x : CoordinateSpace) (hx : x ∈ (c.transition d).source) :
    fixedCovariantJet R H c x =
      TensorCoordinateChange.pullback3 (derivativeMatrix (fderiv ℝ (c.transition d) x))
        (fixedCovariantJet R H d (c.transition d x)) := by
  unfold fixedCovariantJet
  rw [fixedForm_connection_change R hR hs hn c d x hx, fixedForm_jet_change H hH c d x hx,
    fixedForm_matrix_change H c d hx]
  exact CovariantJetNaturality.covariantJet_transformed _ _ _ _ _ (fixedDerivativeMatrix_isUnit c d hx)

/-- The fixed-chart array is the same intrinsic tensor used to define the
paper's auxiliary covariant derivative, evaluated in the actual chart basis. -/
theorem fixedCovariantJet_intrinsic_components (r : Metric (M := M)) (H : Field (M := M))
    (hH : IsSmooth H) (c : AtlasChart M) (m : M) (hm : m ∈ c.chart.source) (a b e : Index) :
    fixedCovariantJet r.inner H c (c.chart m) a b e =
      IntrinsicCov2.tensor r.inner H m
        ![chartTangentBasis c m hm a, chartTangentBasis c m hm b, chartTangentBasis c m hm e] := by
  let d : AtlasChart M := .atPoint m
  let x := c.chart m
  let y := chartAt CoordinateSpace m m
  have hd : m ∈ d.chart.source := mem_chart_source _ m
  have hx : x ∈ (c.transition d).source := by
    refine ⟨c.chart.mapsTo hm, ?_⟩
    change c.chart.symm (c.chart m) ∈ d.chart.source
    rwa [c.chart.left_inv hm]
  have hy : c.transition d x = y := by
    change d.chart (c.chart.symm (c.chart m)) = y
    rw [c.chart.left_inv hm]
    rfl
  let F := fderiv ℝ (c.transition d) x
  have hFrame (j : Index) :
      mfderiv Model Model (chartAt CoordinateSpace m) m (chartTangentBasis c m hm j) =
        F (coordinateBasis j) := by
    rw [chartTangentBasis_apply, inverseFrame_change d c m hd hm, inverseFrame_preferred m m hd,
      ContinuousLinearMap.comp_apply, IntrinsicCov2.mfderiv_chart_tangentFrame m m hd]
  have hJet := fixedCovariantJet_change r.inner H (isSmooth_inner r) r.symm
    (GlobalLeviCivita.inner_nondegenerate r) hH c d x hx
  have hyt : y ∈ (chartAt CoordinateSpace m).target := d.chart.mapsTo hd
  rw [hy, fixedCovariantJet_eq_preferred r H m hyt] at hJet
  simp only [IntrinsicCov2.tensor, IntrinsicCov2.tensorInChart,
    ContinuousMultilinearMap.compContinuousLinearMap_apply, IntrinsicCov2.coordinateTrilinear_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two]
  change fixedCovariantJet r.inner H c x a b e =
    AffineConnection.cov2Differential (computedConnection (coordinateBilinear r.inner m))
      (metricComponents (coordinateBilinear H m)) y
      (mfderiv Model Model (chartAt CoordinateSpace m) m (chartTangentBasis c m hm a))
      (mfderiv Model Model (chartAt CoordinateSpace m) m (chartTangentBasis c m hm b))
      (mfderiv Model Model (chartAt CoordinateSpace m) m (chartTangentBasis c m hm e))
  rw [hFrame a, hFrame b, hFrame e, IntrinsicCov2.trilinear_basis_expansion]
  simp only [IntrinsicCov2.cov2Differential_coordinateBasis]
  exact (congrFun (congrFun (congrFun hJet a) b) e).trans
    (TensorCoordinateChange.pullback3_apply (derivativeMatrix F) _ a b e)

end Burnett.Geometry.MaximalChart
