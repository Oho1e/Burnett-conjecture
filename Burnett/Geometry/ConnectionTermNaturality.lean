import Burnett.Geometry.MetricJetNaturality
import Burnett.Geometry.ChartVectorField

/-!
# Nonlinear connection terms on actual coordinate vectors

The coefficient transformation is extended to a genuine bilinear vector
identity. It applies to any actual smooth symmetric nondegenerate fiber
bilinear field, without positive definiteness. The auxiliary Riemannian
metric is a specialization. The nonlinear correction is the true Hessian
of the same chart transition. No connection transformation law or Hessian
identification is supplied as an input.
-/

noncomputable section

namespace Burnett.Geometry.ConnectionTermNaturality
open Burnett.Geometry.ChartVolume Burnett.Geometry.ManifoldMetric
open Matrix
open scoped BigOperators Topology Manifold ContDiff
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CoordinateCovariantDerivative
open Burnett.Geometry.AffineConnection Burnett.Geometry.MetricJetNaturality
open Burnett.Geometry.ConnectionCoordinateChange

def connectionBilinear (Γ : Connection) : CoordinateSpace →ₗ[ℝ] CoordinateSpace →ₗ[ℝ] CoordinateSpace :=
  LinearMap.mk₂ ℝ (connectionTerm Γ)
    (connectionTerm_add_left Γ) (connectionTerm_smul_left Γ)
    (connectionTerm_add_right Γ) (connectionTerm_smul_right Γ)

@[simp] theorem connectionBilinear_apply (Γ : Connection) (v w : CoordinateSpace) :
    connectionBilinear Γ v w = connectionTerm Γ v w := rfl

@[simp] theorem connectionTerm_coordinateBasis (Γ : Connection) (b c a : Index) :
    connectionTerm Γ (coordinateBasis b) (coordinateBasis c) a = Γ a b c := by
  simpa only [coordinateBasis, OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using
    connectionTerm_basis Γ b c a

theorem linear_apply_eq_sum (L : CoordinateSpace →L[ℝ] CoordinateSpace) (v : CoordinateSpace) (a : Index) :
    (L v) a = ∑ i, derivativeMatrix L a i * v i := by
  have hh := LinearMap.toMatrix_mulVec_repr coordinateBasis coordinateBasis L.toLinearMap v
  have hh' := congrFun hh a
  simpa [derivativeMatrix, coordinateBasis, EuclideanSpace.basisFun_repr, Matrix.mulVec, dotProduct] using hh'.symm

theorem transformed_connection_matrix_cancel (A : Matrix Index Index ℝ)
    (Γ H : Connection) (hA : IsUnit A) (b : Index) :
    A * connectionMatrix (transformedConnection A Γ H) b =
      directionalConnection A Γ b * A + connectionMatrix H b := by
  change A * (A⁻¹ * (directionalConnection A Γ b * A + connectionMatrix H b)) = _
  rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA), Matrix.one_mul]

theorem directionalConnection_basis (L : CoordinateSpace →L[ℝ] CoordinateSpace)
    (Γ : Connection) (b c a : Index) :
    (directionalConnection (derivativeMatrix L) Γ b * derivativeMatrix L) a c =
      connectionTerm Γ (L (coordinateBasis b)) (L (coordinateBasis c)) a := by
  simp only [Matrix.mul_apply, directionalConnection, Matrix.sum_apply, Matrix.smul_apply,
    connectionMatrix, smul_eq_mul, Finset.sum_mul, connectionTerm_apply, derivativeMatrix_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem connectionTerm_transformed (L : CoordinateSpace →L[ℝ] CoordinateSpace)
    (Γ H : Connection) (hA : IsUnit (derivativeMatrix L)) (v w : CoordinateSpace) :
    L (connectionTerm (transformedConnection (derivativeMatrix L) Γ H) v w) =
      connectionTerm Γ (L v) (L w) + connectionTerm H v w := by
  have heq : (connectionBilinear (transformedConnection (derivativeMatrix L) Γ H)).compr₂ L.toLinearMap =
      (connectionBilinear Γ).compl₁₂ L.toLinearMap L.toLinearMap + connectionBilinear H := by
    apply coordinateBasis.ext
    intro b
    apply coordinateBasis.ext
    intro c
    ext a
    change (L (connectionTerm (transformedConnection (derivativeMatrix L) Γ H)
      (coordinateBasis b) (coordinateBasis c))) a =
      (connectionTerm Γ (L (coordinateBasis b)) (L (coordinateBasis c))) a +
      (connectionTerm H (coordinateBasis b) (coordinateBasis c)) a
    rw [linear_apply_eq_sum]
    simp only [connectionTerm_coordinateBasis]
    have hm := congrArg (fun Q : Matrix Index Index ℝ => Q a c)
      (transformed_connection_matrix_cancel (derivativeMatrix L) Γ H hA b)
    dsimp only at hm
    rw [Matrix.add_apply, directionalConnection_basis] at hm
    exact hm
  exact congrArg (fun F : CoordinateSpace →ₗ[ℝ] CoordinateSpace →ₗ[ℝ] CoordinateSpace => F v w) heq


variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem coordinateBilinear_connection_change (B : ManifoldBilinear.Field (M := M))
    (hc : ManifoldBilinear.IsSmooth B) (hs : ManifoldBilinear.IsSymmetric B)
    (hn : ManifoldBilinear.IsNondegenerate B) (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) :
    BackgroundConnection.computedConnection (ManifoldMetricTransition.coordinateBilinear B c) x =
      transformedConnection (derivativeMatrix (fderiv ℝ (chartTransition c d) x))
        (BackgroundConnection.computedConnection (ManifoldMetricTransition.coordinateBilinear B d)
          (chartTransition c d x)) (ActualChartSecondJet.actualHessian c d x) := by
  let e := chartTransition c d
  let A := derivativeMatrix (fderiv ℝ e x)
  let G : Matrix Index Index ℝ := metricComponents (ManifoldMetricTransition.coordinateBilinear B d) (e x)
  let J := coordinateJet (metricComponents (ManifoldMetricTransition.coordinateBilinear B d)) (e x)
  have hy : e x ∈ (chartAt CoordinateSpace d).target := (e.mapsTo hx).1
  have ha0 := ManifoldTensorNorm.transitionMatrix_isUnit c d
    ((chartAt CoordinateSpace c).symm x) ((chartAt CoordinateSpace c).symm_mapsTo hx.1) hx.2
  have hA : IsUnit A := by
    simpa only [(chartAt CoordinateSpace c).right_inv hx.1] using ha0
  have hdet : G.det ≠ 0 := by
    change Matrix.det (metricComponents (ManifoldMetricTransition.coordinateBilinear B d) (e x)) ≠ 0
    rw [ManifoldMetricTransition.metricComponents_eq_toMatrix]
    exact (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero coordinateBasis).mp
      (ManifoldBilinear.coordinateBilinear_nondegenerate B hn d hy)
  have hG : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hg : IsSymmetricTensor G := FiberMetric.covariant_symmetric _
    (ManifoldBilinear.coordinateBilinear_symmetric B hs d (e x)) coordinateBasis
  have hJ : ∀ b, IsSymmetricTensor (J b) := coordinateJet_symmetric _ (e x)
    (Filter.Eventually.of_forall (fun y => FiberMetric.covariant_symmetric _
      (ManifoldBilinear.coordinateBilinear_symmetric B hs d y) coordinateBasis))
  have ht := transformed_christoffel A G J (ActualChartSecondJet.actualHessian c d x) hA hG hg hJ
    (ActualChartSecondJet.actualHessian_symmetric c d x hx)
  have hm := ManifoldMetricTransition.coordinateBilinear_matrix_change B c d hx
  have hj := coordinateBilinear_jet_change B hc c d x hx
  simpa only [BackgroundConnection.computedConnection, InverseField.matrixInverse, hm, hj,
    TensorCoordinateChange.pullbackMetric] using ht.symm


theorem chartJacobian_isUnit (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) :
    IsUnit (derivativeMatrix (fderiv ℝ (chartTransition c d) x)) := by
  have ha := ManifoldTensorNorm.transitionMatrix_isUnit c d
    ((chartAt CoordinateSpace c).symm x) ((chartAt CoordinateSpace c).symm_mapsTo hx.1) hx.2
  simpa only [(chartAt CoordinateSpace c).right_inv hx.1] using ha

theorem coordinateBilinear_connectionTerm_change (B : ManifoldBilinear.Field (M := M))
    (hc : ManifoldBilinear.IsSmooth B) (hs : ManifoldBilinear.IsSymmetric B)
    (hn : ManifoldBilinear.IsNondegenerate B) (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) (v w : CoordinateSpace) :
    fderiv ℝ (chartTransition c d) x
      (connectionTerm (BackgroundConnection.computedConnection
        (ManifoldMetricTransition.coordinateBilinear B c) x) v w) =
      connectionTerm (BackgroundConnection.computedConnection
        (ManifoldMetricTransition.coordinateBilinear B d) (chartTransition c d x))
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) +
        fderiv ℝ (fderiv ℝ (chartTransition c d)) x v w := by
  rw [coordinateBilinear_connection_change B hc hs hn c d x hx]
  have ht := connectionTerm_transformed (fderiv ℝ (chartTransition c d) x)
    (BackgroundConnection.computedConnection (ManifoldMetricTransition.coordinateBilinear B d)
      (chartTransition c d x)) (ActualChartSecondJet.actualHessian c d x)
    (chartJacobian_isUnit c d x hx) v w
  rw [ChartVectorField.connectionTerm_actualHessian] at ht
  exact ht

theorem coordinateMetric_connectionTerm_change (r : Metric (M := M)) (c d : M)
    (x : CoordinateSpace) (hx : x ∈ (chartTransition c d).source) (v w : CoordinateSpace) :
    fderiv ℝ (chartTransition c d) x
      (connectionTerm (BackgroundConnection.computedConnection (coordinateMetric r c) x) v w) =
      connectionTerm (BackgroundConnection.computedConnection (coordinateMetric r d) (chartTransition c d x))
        (fderiv ℝ (chartTransition c d) x v) (fderiv ℝ (chartTransition c d) x w) +
        fderiv ℝ (fderiv ℝ (chartTransition c d)) x v w := by
  rw [coordinateMetric_connection_change r c d x hx]
  have ht := connectionTerm_transformed (fderiv ℝ (chartTransition c d) x)
    (BackgroundConnection.computedConnection (coordinateMetric r d) (chartTransition c d x))
    (ActualChartSecondJet.actualHessian c d x) (chartJacobian_isUnit c d x hx) v w
  rw [ChartVectorField.connectionTerm_actualHessian] at ht
  exact ht

end Burnett.Geometry.ConnectionTermNaturality
