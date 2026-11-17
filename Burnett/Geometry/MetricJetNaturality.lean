import Burnett.Geometry.ActualChartSecondJet
import Burnett.Geometry.ConnectionCoordinateChange
import Burnett.Geometry.ManifoldTensorNorm

/-!
# Actual first metric jets under a smooth nonlinear chart transition

The Jacobian and Hessian are genuine Frechet derivatives of the preferred
chart transition. Differentiating the same fiberwise bilinear field on the
open overlap produces all three transformed-jet terms. For the same actual
auxiliary Riemannian metric, this identifies the computed Christoffel
connections in the two charts, including the nonlinear Hessian term.
No metric-jet transformation identity is an input. Global connection
construction and covariant differentiation of manifold sections are separate.
-/

noncomputable section
namespace Burnett.Geometry.MetricJetNaturality
open scoped BigOperators Topology Manifold ContDiff
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ActualChartSecondJet
open Burnett.Geometry.AffineConnection Burnett.Geometry.CoordinateCovariantDerivative
open Burnett.Geometry.ConnectionCoordinateChange

@[simp] theorem derivativeMatrix_apply (L : CoordinateSpace →L[ℝ] CoordinateSpace)
    (a c : Index) : derivativeMatrix L a c = (L (coordinateBasis c)) a := by
  simp [derivativeMatrix, LinearMap.toMatrix_apply, coordinateBasis, EuclideanSpace.basisFun_repr]

theorem jacobian_entry_differentiable (φ : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace)
    (hJ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a c : Index) :
    DifferentiableAt ℝ (fun y => derivativeMatrix (fderiv ℝ φ y) a c) x := by
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ φ y (coordinateBasis c)) x :=
    hJ.clm_apply (differentiableAt_const (coordinateBasis c))
  simpa only [derivativeMatrix_apply] using component_differentiable hc a

theorem fderiv_jacobian_entry (φ : CoordinateSpace → CoordinateSpace) (x v : CoordinateSpace)
    (hJ : DifferentiableAt ℝ (fderiv ℝ φ) x) (a c : Index) :
    fderiv ℝ (fun y => derivativeMatrix (fderiv ℝ φ y) a c) x v =
      ((fderiv ℝ (fderiv ℝ φ) x v) (coordinateBasis c)) a := by
  have hc : DifferentiableAt ℝ (fun y => fderiv ℝ φ y (coordinateBasis c)) x :=
    hJ.clm_apply (differentiableAt_const (coordinateBasis c))
  simp only [derivativeMatrix_apply]
  rw [fderiv_component hc, fderiv_clm_apply hJ (differentiableAt_const (coordinateBasis c))]
  simp

theorem directionalTensor_comp (G : CoordinateSpace → Tensor2)
    (φ : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace)
    (hG : DifferentiableComponentsAt G (φ x)) (hφ : DifferentiableAt ℝ φ x) (b : Index) :
    directionalTensor (fun y => G (φ y)) x (coordinateBasis b) =
      ∑ p, derivativeMatrix (fderiv ℝ φ x) p b • coordinateJet G (φ x) p := by
  ext a c
  simp only [directionalTensor, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  change fderiv ℝ ((fun z => G z a c) ∘ φ) x (coordinateBasis b) = _
  rw [fderiv_comp x (hG a c) hφ, ContinuousLinearMap.comp_apply]
  have heq : fderiv ℝ φ x (coordinateBasis b) =
      ∑ p, derivativeMatrix (fderiv ℝ φ x) p b • coordinateBasis p := by
    simpa [derivativeMatrix_apply, coordinateBasis, EuclideanSpace.basisFun_repr] using
      (coordinateBasis.sum_repr (fderiv ℝ φ x (coordinateBasis b))).symm
  rw [heq]
  simp [map_sum, map_smul, coordinateJet, coordinateBasis, EuclideanSpace.basisFun_apply]


theorem fderiv_jacobian_column (φ : CoordinateSpace → CoordinateSpace) (x v : CoordinateSpace)
    (hJ : DifferentiableAt ℝ (fderiv ℝ φ) x) (c : Index) :
    fderiv ℝ (fun y => fderiv ℝ φ y (coordinateBasis c)) x v =
      fderiv ℝ (fderiv ℝ φ) x v (coordinateBasis c) := by
  rw [fderiv_clm_apply hJ (differentiableAt_const (coordinateBasis c))]
  simp

theorem matrix_triple_entry (P G Q : Matrix Index Index ℝ) (i j : Index) :
    (P.transpose * G * Q) i j = ∑ a, ∑ b, P a i * G a b * Q b j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]


theorem differentiableAt_chartJacobian (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) :
    DifferentiableAt ℝ (fderiv ℝ (chartTransition c d)) x := by
  have hc2 : ContDiffAt ℝ 2 (chartTransition c d) x :=
    ((contDiffOn_chartTransition_infty c d).contDiffAt
      ((chartTransition c d).open_source.mem_nhds hx)).of_le (by
      change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  exact (hc2.fderiv_right (m := 1) (by norm_num)).differentiableAt_one

theorem fderiv_chartJacobian_entry (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) (a b e : Index) :
    fderiv ℝ (fun y => derivativeMatrix (fderiv ℝ (chartTransition c d) y) a e)
      x (coordinateBasis b) = actualHessian c d x a b e :=
  fderiv_jacobian_entry _ x (coordinateBasis b) (differentiableAt_chartJacobian c d x hx) a e

/-- The actual same-field metric jet transforms with both Hessian terms. -/
theorem coordinateBilinear_jet_change (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) :
    coordinateJet (metricComponents (coordinateBilinear B c)) x =
      transformedJet (derivativeMatrix (fderiv ℝ (chartTransition c d) x))
        (metricComponents (coordinateBilinear B d) (chartTransition c d x))
        (coordinateJet (metricComponents (coordinateBilinear B d)) (chartTransition c d x))
        (actualHessian c d x) := by
  let e := chartTransition c d
  let G := metricComponents (coordinateBilinear B d)
  have hy : e x ∈ (chartAt CoordinateSpace d).target := (e.mapsTo hx).1
  have hφ : DifferentiableAt ℝ e x :=
    (((contDiffOn_chartTransition c d).differentiableOn le_rfl) x hx).differentiableAt
      (e.open_source.mem_nhds hx)
  have hJ : DifferentiableAt ℝ (fderiv ℝ e) x := differentiableAt_chartJacobian c d x hx
  have hG : DifferentiableComponentsAt G (e x) := by
    intro a b
    exact (((ManifoldBilinear.contDiffOn_metricComponents_one B hB d a b).differentiableOn le_rfl)
      (e x) hy).differentiableAt ((chartAt CoordinateSpace d).open_target.mem_nhds hy)
  have hcomp : DifferentiableComponentsAt (fun y => G (e y)) x :=
    fun a b => (hG a b).comp x hφ
  have hcol (a : Index) : DifferentiableAt ℝ (fun y => fderiv ℝ e y (coordinateBasis a)) x :=
    hJ.clm_apply (differentiableAt_const (coordinateBasis a))
  funext b i j
  have heq : (fun y => metricComponents (coordinateBilinear B c) y i j) =ᶠ[𝓝 x]
      (fun y => tensorForm (G (e y)) (fderiv ℝ e y (coordinateBasis i))
        (fderiv ℝ e y (coordinateBasis j))) := by
    filter_upwards [e.open_source.mem_nhds hx] with y hy
    dsimp only [G, e]
    simp only [tensorForm_metricComponents]
    exact coordinateBilinear_change_apply B c d hy (coordinateBasis i) (coordinateBasis j)
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
    connectionMatrix, actualHessian, derivativeMatrix_apply, tensorForm_apply] using hd


theorem coordinateMetric_jet_change (r : Metric (M := M)) (c d : M)
    (x : CoordinateSpace) (hx : x ∈ (chartTransition c d).source) :
    coordinateJet (metricComponents (coordinateMetric r c)) x =
      transformedJet (derivativeMatrix (fderiv ℝ (chartTransition c d) x))
        (metricComponents (coordinateMetric r d) (chartTransition c d x))
        (coordinateJet (metricComponents (coordinateMetric r d)) (chartTransition c d x))
        (actualHessian c d x) :=
  coordinateBilinear_jet_change r.inner (ManifoldBilinear.isSmooth_inner r) c d x hx

/-- c is the new chart, d the old chart; the Jacobian maps c vectors to d vectors. -/
theorem coordinateMetric_connection_change (r : Metric (M := M)) (c d : M)
    (x : CoordinateSpace) (hx : x ∈ (chartTransition c d).source) :
    BackgroundConnection.computedConnection (coordinateMetric r c) x =
      transformedConnection (derivativeMatrix (fderiv ℝ (chartTransition c d) x))
        (BackgroundConnection.computedConnection (coordinateMetric r d) (chartTransition c d x))
        (actualHessian c d x) := by
  let e := chartTransition c d
  let A := derivativeMatrix (fderiv ℝ e x)
  let G : Matrix Index Index ℝ := metricComponents (coordinateMetric r d) (e x)
  let J := coordinateJet (metricComponents (coordinateMetric r d)) (e x)
  have hy : e x ∈ (chartAt CoordinateSpace d).target := (e.mapsTo hx).1
  have ha0 := ManifoldTensorNorm.transitionMatrix_isUnit c d
    ((chartAt CoordinateSpace c).symm x) ((chartAt CoordinateSpace c).symm_mapsTo hx.1) hx.2
  have hA : IsUnit A := by
    simpa only [(chartAt CoordinateSpace c).right_inv hx.1] using ha0
  have hG : G.PosDef := ManifoldMetric.coordinateMetric_posDef r d hy
  have hg : IsSymmetricTensor G :=
    FiberMetric.covariant_symmetric _ (ManifoldMetric.coordinateMetric_symm r d (e x)) coordinateBasis
  have hJ : ∀ b, IsSymmetricTensor (J b) :=
    coordinateJet_symmetric _ (e x) (Filter.Eventually.of_forall
      (fun y => FiberMetric.covariant_symmetric _ (ManifoldMetric.coordinateMetric_symm r d y) coordinateBasis))
  have ht := transformed_christoffel A G J (actualHessian c d x) hA hG.isUnit hg hJ
    (actualHessian_symmetric c d x hx)
  have hm := coordinateMetric_matrix_change r c d hx
  have hj := coordinateMetric_jet_change r c d x hx
  simpa only [BackgroundConnection.computedConnection, InverseField.matrixInverse, hm, hj,
    TensorCoordinateChange.pullbackMetric] using ht.symm

end Burnett.Geometry.MetricJetNaturality
