import Burnett.Geometry.MaximalChart.ConnectionTransfer

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.MaximalChart

open Set Filter Function LinearMap Burnett.RicciSymbol
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ManifoldMetricTransition
open scoped Manifold ContDiff Topology Matrix
open BackgroundConnection ConnectionTermNaturality CoordinateCovariantDerivative

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

variable [SecondCountableTopology M]

omit [IsManifold Model ∞ M] [SecondCountableTopology M] in
private theorem connectionTerm_fixedHessian (c d : AtlasChart M)
    (x u v : CoordinateSpace) :
    connectionTerm (fixedHessian c d x) u v =
      fderiv ℝ (fderiv ℝ (c.transition d)) x u v := by
  let L := fderiv ℝ (fderiv ℝ (c.transition d)) x
  let H : CoordinateSpace →ₗ[ℝ] CoordinateSpace →ₗ[ℝ] CoordinateSpace :=
    LinearMap.mk₂ ℝ (fun a b => L a b)
      (by intros; simp [map_add]) (by intros; simp [map_smul])
      (by intros; simp [map_add]) (by intros; simp [map_smul])
  have h : connectionBilinear (fixedHessian c d x) = H := by
    apply coordinateBasis.ext
    intro b
    apply coordinateBasis.ext
    intro k
    ext a
    rw [connectionBilinear_apply, connectionTerm_coordinateBasis]
    rfl
  exact congrArg (fun F : CoordinateSpace →ₗ[ℝ] CoordinateSpace →ₗ[ℝ] CoordinateSpace => F u v) h

theorem fixedForm_connectionTerm_change
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ManifoldBilinear.IsSymmetric B) (hn : ManifoldBilinear.IsNondegenerate B)
    (c d : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ (c.transition d).source) (u v : CoordinateSpace) :
    fderiv ℝ (c.transition d) x (connectionTerm (computedConnection (fixedForm B c) x) u v) =
      connectionTerm (computedConnection (fixedForm B d) (c.transition d x))
        (fderiv ℝ (c.transition d) x u) (fderiv ℝ (c.transition d) x v) +
      fderiv ℝ (fderiv ℝ (c.transition d)) x u v := by
  let L := fderiv ℝ (c.transition d) x
  rw [fixedForm_connection_change B hB hs hn c d x hx]
  simpa only [L, connectionTerm_fixedHessian] using
    connectionTerm_transformed L (computedConnection (fixedForm B d) (c.transition d x))
      (fixedHessian c d x) (fixedDerivativeMatrix_isUnit c d hx) u v

/-- Covariant derivatives of the same two local fields in the two fixed
charts have the chart transition law of a vector. -/
theorem fixedForm_derivative_change
    (B : ManifoldBilinear.Field (M := M)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ManifoldBilinear.IsSymmetric B) (hn : ManifoldBilinear.IsNondegenerate B)
    (c d : AtlasChart M) (x : CoordinateSpace)
    (hx : x ∈ (c.transition d).source)
    (U V U' V' : CoordinateSpace → CoordinateSpace)
    (hV : DifferentiableAt ℝ V x) (hV' : DifferentiableAt ℝ V' (c.transition d x))
    (hU : U' (c.transition d x) = fderiv ℝ (c.transition d) x (U x))
    (hRel : (fun y => V' (c.transition d y)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (c.transition d) y (V y))) :
    fderiv ℝ (c.transition d) x
        (derivative (computedConnection (fixedForm B c)) U V x) =
      derivative (computedConnection (fixedForm B d)) U' V' (c.transition d x) := by
  let e := c.transition d
  have hOrder : (2 : WithTop ℕ∞) ≤ ∞ :=
    WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤)
  have h₂ : ContDiffAt ℝ 2 e x :=
    ((c.smooth_transition d).contDiffAt (e.open_source.mem_nhds hx)).of_le hOrder
  have he : DifferentiableAt ℝ e x := h₂.differentiableAt (by norm_num)
  have hDe : DifferentiableAt ℝ (fderiv ℝ e) x :=
    (h₂.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hChain : (fderiv ℝ (fun y => V' (e y)) x) (U x) =
      fderiv ℝ V' (e x) (fderiv ℝ e x (U x)) := by
    rw [fderiv_comp' x hV' he, ContinuousLinearMap.comp_apply]
  have hProduct : (fderiv ℝ (fun y => fderiv ℝ e y (V y)) x) (U x) =
      fderiv ℝ e x (fderiv ℝ V x (U x)) + fderiv ℝ (fderiv ℝ e) x (U x) (V x) := by
    rw [fderiv_clm_apply hDe hV]
    rfl
  have h := hChain.symm.trans ((congrArg (fun L : CoordinateSpace →L[ℝ] CoordinateSpace =>
      L (U x)) hRel.fderiv_eq).trans hProduct)
  have hHere : V' (e x) = fderiv ℝ e x (V x) := hRel.eq_of_nhds
  change fderiv ℝ e x (fderiv ℝ V x (U x) +
      connectionTerm (computedConnection (fixedForm B c) x) (U x) (V x)) =
    fderiv ℝ V' (e x) (U' (e x)) +
      connectionTerm (computedConnection (fixedForm B d) (e x)) (U' (e x)) (V' (e x))
  rw [hU, hHere, h, map_add, fixedForm_connectionTerm_change B hB hs hn c d x hx]
  abel

end Burnett.Geometry.MaximalChart
