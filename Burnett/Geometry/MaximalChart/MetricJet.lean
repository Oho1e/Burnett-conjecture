import Burnett.Geometry.MaximalChart.MetricCoordinates

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open AffineConnection CoordinateCovariantDerivative ConnectionCoordinateChange MetricJetNaturality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

def fixedHessian (c d : AtlasChart M) (x : CoordinateSpace) : Connection :=
  fun a b e => ((fderiv ℝ (fderiv ℝ (c.transition d)) x (coordinateBasis b)) (coordinateBasis e)) a

variable [SecondCountableTopology M]

theorem fixedForm_jet_change (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (c d : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ (c.transition d).source) :
    coordinateJet (metricComponents (fixedForm B c)) x =
      transformedJet (derivativeMatrix (fderiv ℝ (c.transition d) x))
        (metricComponents (fixedForm B d) (c.transition d x))
        (coordinateJet (metricComponents (fixedForm B d)) (c.transition d x))
        (fixedHessian c d x) := by
  let e := c.transition d
  let G := metricComponents (fixedForm B d)
  have hy : e x ∈ d.chart.target := (e.mapsTo hx).1
  have hφ : DifferentiableAt ℝ e x :=
    (((c.smooth_transition d).differentiableOn (by simp)) x hx).differentiableAt
      (e.open_source.mem_nhds hx)
  have hJ : DifferentiableAt ℝ (fderiv ℝ e) x := ((c.smooth_transition d).fderiv_of_isOpen e.open_source (by simp : ∞ + 1 ≤ (∞ : WithTop ℕ∞))).contDiffAt (e.open_source.mem_nhds hx) |>.differentiableAt (by simp)
  have hG : DifferentiableComponentsAt G (e x) := by
    intro a b
    exact (((fixedForm_components_smooth B hB d a b).differentiableOn (by simp))
      (e x) hy).differentiableAt (d.chart.open_target.mem_nhds hy)
  have hcomp : DifferentiableComponentsAt (fun y => G (e y)) x :=
    fun a b => (hG a b).comp x hφ
  have hcol (a : Index) : DifferentiableAt ℝ (fun y => fderiv ℝ e y (coordinateBasis a)) x :=
    hJ.clm_apply (differentiableAt_const (coordinateBasis a))
  funext b i j
  have heq : (fun y => metricComponents (fixedForm B c) y i j) =ᶠ[𝓝 x]
      (fun y => tensorForm (G (e y)) (fderiv ℝ e y (coordinateBasis i))
        (fderiv ℝ e y (coordinateBasis j))) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    dsimp only [G, e]
    simp only [tensorForm_metricComponents]
    exact fixedCoordinateBilinear_change B c d hy (coordinateBasis i) (coordinateBasis j)
  have hd := congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (coordinateBasis b)) heq.fderiv_eq
  dsimp only at hd
  rw [fderiv_tensorForm (fun y => G (e y))
    (fun y => fderiv ℝ e y (coordinateBasis i))
    (fun y => fderiv ℝ e y (coordinateBasis j)) x (coordinateBasis b) hcomp (hcol i) (hcol j),
    fderiv_jacobian_column e x (coordinateBasis b) hJ i,
    fderiv_jacobian_column e x (coordinateBasis b) hJ j,
    directionalTensor_comp G e x hG hφ b] at hd
  simpa only [coordinateJet, coordinateBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply,
    transformedJet, transformedMetricDerivative, Matrix.add_apply, matrix_triple_entry,
    connectionMatrix, fixedHessian, derivativeMatrix_apply, tensorForm_apply] using hd

end Burnett.Geometry.MaximalChart
