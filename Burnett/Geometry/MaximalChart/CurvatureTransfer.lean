import Burnett.Geometry.MaximalChart.DerivativeTransfer
import Burnett.Geometry.IntrinsicRicciTrace

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open BackgroundConnection AffineConnection MetricJetNaturality CoordinateCovariantDerivative

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

variable [SecondCountableTopology M]

theorem fixedForm_connection_smooth
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hn : ManifoldBilinear.IsNondegenerate B) (c : AtlasChart M) :
    ContDiffOn ℝ ∞ (computedConnection (fixedForm B c)) c.chart.target := by
  apply SmoothMetricConnection.contDiffOn_computedConnection_field _ _ c.chart.open_target
    (fixedForm_components_smooth B hB c)
  intro x hx
  apply (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero coordinateBasis).2
  rw [← metricComponents_eq_toMatrix]
  exact fixedForm_det_ne_zero B hn c hx

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
private theorem fixedForm_connection_torsionFree
    (B : ManifoldBilinear.Field (M := M)) (hs : ManifoldBilinear.IsSymmetric B)
    (c : AtlasChart M) (x : CoordinateSpace) (a b k : Index) :
    computedConnection (fixedForm B c) x a b k = computedConnection (fixedForm B c) x a k b := by
  apply christoffel_torsion_free _ _
  exact coordinateJet_symmetric _ x (Eventually.of_forall (fun y i j => hs (c.chart.symm y) _ _))

/-- The local curvature expressions agree under the same chart transition
as the covariant derivative. Only germs on the overlap enter. -/
theorem fixedForm_coordinateCurvature_change
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ManifoldBilinear.IsSymmetric B) (hn : ManifoldBilinear.IsNondegenerate B)
    (c d : AtlasChart M)
    (X Y Z X' Y' Z' : CoordinateSpace → CoordinateSpace) :
    let e := c.transition d
    let Rel (F F' : CoordinateSpace → CoordinateSpace) :=
      ∀ x ∈ e.source, F' (e x) = fderiv ℝ e x (F x)
    ContDiffOn ℝ ∞ X e.source → ContDiffOn ℝ ∞ Y e.source → ContDiffOn ℝ ∞ Z e.source →
    ContDiffOn ℝ ∞ X' e.target → ContDiffOn ℝ ∞ Y' e.target → ContDiffOn ℝ ∞ Z' e.target →
    Rel X X' → Rel Y Y' → Rel Z Z' →
    ∀ x ∈ e.source,
      fderiv ℝ e x (IntrinsicCurvature.coordinateCurvature (computedConnection (fixedForm B c)) X Y Z x) =
        IntrinsicCurvature.coordinateCurvature (computedConnection (fixedForm B d)) X' Y' Z' (e x) := by
  intro e Rel hX hY hZ hX' hY' hZ' rX rY rZ
  let Γc := computedConnection (fixedForm B c)
  let Γd := computedConnection (fixedForm B d)
  let Dc := derivative Γc
  let Dd := derivative Γd
  have hΓc : ContDiffOn ℝ ∞ Γc e.source :=
    (fixedForm_connection_smooth B hB hn c).mono (fun _ hx => hx.1)
  have hΓd : ContDiffOn ℝ ∞ Γd e.target :=
    (fixedForm_connection_smooth B hB hn d).mono (fun _ hx => hx.1)
  have hDc := GlobalCovariantDerivative.contDiffOn_coordinateAffineDerivative e.open_source Γc
  have hDd := GlobalCovariantDerivative.contDiffOn_coordinateAffineDerivative e.open_target Γd
  have hD (U V U' V' : CoordinateSpace → CoordinateSpace) (rU : Rel U U') (rV : Rel V V')
      (hV : ContDiffOn ℝ ∞ V e.source) (hV' : ContDiffOn ℝ ∞ V' e.target) :
      Rel (Dc U V) (Dd U' V') := by
    intro x hx
    have hx' : e x ∈ e.target := e.mapsTo hx
    apply Eq.symm
    apply fixedForm_derivative_change B hB hs hn c d x hx U V U' V'
    · exact (hV.contDiffAt (e.open_source.mem_nhds hx)).differentiableAt (by simp)
    · exact (hV'.contDiffAt (e.open_target.mem_nhds hx')).differentiableAt (by simp)
    · exact rU x hx
    · filter_upwards [e.open_source.mem_nhds hx] with y hy using rV y hy
  have rYZ := hD _ _ _ _ rY rZ hZ hZ'
  have rXZ := hD _ _ _ _ rX rZ hZ hZ'
  have rLie : Rel (_root_.VectorField.lieBracket ℝ X Y) (_root_.VectorField.lieBracket ℝ X' Y') := by
    intro x hx
    rw [← derivative_torsion_free Γc X Y x (fixedForm_connection_torsionFree B hs c x),
      ← derivative_torsion_free Γd X' Y' (e x) (fixedForm_connection_torsionFree B hs d (e x)),
      map_sub]
    exact congrArg₂ Sub.sub (hD _ _ _ _ rX rY hY hY' x hx) (hD _ _ _ _ rY rX hX hX' x hx)
  intro x hx
  have h₁ := hD _ _ _ _ rX rYZ (hDc Y Z hΓc hY hZ) (hDd Y' Z' hΓd hY' hZ') x hx
  have h₂ := hD _ _ _ _ rY rXZ (hDc X Z hΓc hX hZ) (hDd X' Z' hΓd hX' hZ') x hx
  have h₃ := hD _ _ _ _ rLie rZ hZ hZ' x hx
  change fderiv ℝ e x (Dc X (Dc Y Z) x - Dc Y (Dc X Z) x -
      Dc (_root_.VectorField.lieBracket ℝ X Y) Z x) =
    Dd X' (Dd Y' Z') (e x) - Dd Y' (Dd X' Z') (e x) - Dd (_root_.VectorField.lieBracket ℝ X' Y') Z' (e x)
  rw [map_sub, map_sub, ← h₁, ← h₂, ← h₃]

end Burnett.Geometry.MaximalChart
