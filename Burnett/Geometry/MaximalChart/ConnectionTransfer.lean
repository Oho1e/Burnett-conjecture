import Burnett.Geometry.MaximalChart.MetricJet
import Burnett.Geometry.ConnectionTermNaturality

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open BackgroundConnection AffineConnection ConnectionCoordinateChange MetricJetNaturality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

variable [SecondCountableTopology M]

/-- The computed Christoffel arrays of one intrinsic metric in two fixed
smooth charts obey the exact nonlinear coordinate transformation. -/
theorem fixedForm_connection_change
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ManifoldBilinear.IsSymmetric B) (hn : ManifoldBilinear.IsNondegenerate B)
    (c d : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ (c.transition d).source) :
    computedConnection (fixedForm B c) x =
      transformedConnection (derivativeMatrix (fderiv ℝ (c.transition d) x))
        (computedConnection (fixedForm B d) (c.transition d x))
        (fixedHessian c d x) := by
  let e := c.transition d
  let A := derivativeMatrix (fderiv ℝ e x)
  let G : Matrix Index Index ℝ := metricComponents (fixedForm B d) (e x)
  let J := coordinateJet (metricComponents (fixedForm B d)) (e x)
  have hy : e x ∈ d.chart.target := (e.mapsTo hx).1
  have hA : IsUnit A := by
    apply (Matrix.isUnit_iff_isUnit_det A).2
    rw [isUnit_iff_ne_zero, det_derivativeMatrix]
    exact chartDerivative_det_ne_zero c d x hx
  have hG : IsUnit G := by
    apply (Matrix.isUnit_iff_isUnit_det G).2
    rw [isUnit_iff_ne_zero]
    exact fixedForm_det_ne_zero B hn d hy
  have hSym (y : CoordinateSpace) : IsSymmetricTensor (metricComponents (fixedForm B d) y) := by
    intro a b
    exact hs (d.chart.symm y) _ _
  have hJ : ∀ b, IsSymmetricTensor (J b) :=
    coordinateJet_symmetric _ (e x) (Filter.Eventually.of_forall hSym)
  have hSmooth := (c.smooth_transition d).contDiffAt (e.open_source.mem_nhds hx)
  have hOrder : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have hTwice : ContDiffAt ℝ 2 e x := hSmooth.of_le hOrder
  have hH (a b k : Index) : fixedHessian c d x a b k =
      fixedHessian c d x a k b := by
    exact congrArg (fun z : CoordinateSpace => z a)
      ((hTwice.isSymmSndFDerivAt (by norm_num)).eq (coordinateBasis b) (coordinateBasis k))
  have ht := transformed_christoffel A G J (fixedHessian c d x) hA hG (hSym (e x)) hJ hH
  have hm := fixedForm_matrix_change B c d hx
  have hj := fixedForm_jet_change B hB c d x hx
  simpa only [computedConnection, InverseField.matrixInverse, hm, hj,
    TensorCoordinateChange.pullbackMetric] using ht.symm

end Burnett.Geometry.MaximalChart
