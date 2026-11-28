import Burnett.Analysis.TransportWard.MetricVariation
import Burnett.Geometry.ConnectionCoordinateChange
import Burnett.Geometry.SmoothMetricConnection

/-! Actual spatial derivatives of the inverse metric and its volume density. -/

set_option autoImplicit false
set_option maxHeartbeats 4500000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V02.EinsteinHilbert

open Set Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ConnectionCoordinateChange (connectionMatrix matrix_metric_compatible_iff)
open Burnett.Geometry.InverseField (matrixInverse compose_matrixInverse matrixInverse_compose)
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_det contDiffOn_matrixInverse contDiffOn_coordinateJet)
open scoped BigOperators ContDiff Matrix Matrix.Norms.Elementwise Topology

local notation "E" => CoordinateSpace

/-- Coordinate partial derivative in the frame used by the actual Ricci jet. -/
def coordinatePartial (f : E → ℝ) (x : E) (a : Index) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single a 1)

/-- The computed Christoffel construction applied directly to metric components. -/
def coordinateConnectionFromMetric (g : E → Mat) (x : E) : Connection :=
  christoffel (inverseMatrix (g x)) (coordinateJet g x)

/-- Trace of the connection matrix in one derivative slot. -/
def connectionTrace (Γ : Connection) (a : Index) : ℝ :=
  ∑ b, Γ b a b

theorem contDiffOn_coordinateConnectionFromMetric (g : E → Mat) {U : Set E} (hU : IsOpen U)
    (hg : ∀ b c, ContDiffOn ℝ ∞ (fun y => g y b c) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (a b c : Index) :
    ContDiffOn ℝ ∞ (fun x => coordinateConnectionFromMetric g x a b c) U := by
  have hB := contDiffOn_matrixInverse g U hg hn
  have hJ := contDiffOn_coordinateJet g U hU hg
  unfold coordinateConnectionFromMetric christoffel koszul
  exact ContDiffOn.sum fun d _ => (hB a d).mul
    ((((hJ b c d).add (hJ c b d)).sub (hJ d b c)).div_const 2)

theorem contDiffOn_spatialMetricDensity (g : E → Mat) {U : Set E}
    (hg : ∀ b c, ContDiffOn ℝ ∞ (fun y => g y b c) U)
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) :
    ContDiffOn ℝ ∞ (fun x => metricDensity (g x)) U :=
  ((contDiffOn_det g U hg).abs hn).sqrt (fun x hx => abs_ne_zero.mpr (hn x hx))

theorem inverseMatrix_symmetric (G : Mat) (hG : IsSymmetricTensor G) :
    IsSymmetricTensor (inverseMatrix G) := by
  have ht : Gᵀ = G := by
    ext i j
    exact hG j i
  have hi : G⁻¹ᵀ = G⁻¹ := by rw [Matrix.transpose_nonsing_inv, ht]
  intro i j
  change G⁻¹ i j = G⁻¹ j i
  exact (congrFun (congrFun hi i) j).symm

private theorem differentiableAt_matrixDet (G : Mat) :
    DifferentiableAt ℝ (fun A : Mat => Matrix.det A) G :=
  (detMultilinear.hasFDerivAt G).differentiableAt

private theorem differentiableAt_matrixEntry (G : Mat) (i j : Index) :
    DifferentiableAt ℝ (fun A : Mat => A i j) G := by
  have hi : DifferentiableAt ℝ (fun A : Mat => A i) G := differentiableAt_apply i G
  have hj : DifferentiableAt ℝ (fun A : Index → ℝ => A j) (G i) := differentiableAt_apply j (G i)
  exact hj.comp G hi

private theorem differentiableAt_inverseMatrixEntry (G : Mat) (hG : Matrix.det G ≠ 0) (i j : Index) :
    DifferentiableAt ℝ (fun A : Mat => inverseMatrix A i j) G := by
  let row : Index → ℝ := Pi.single i 1
  have hu : DifferentiableAt ℝ (fun A : Mat => A.updateRow j row) G := by
    apply differentiableAt_pi.mpr
    intro a
    apply differentiableAt_pi.mpr
    intro b
    by_cases ha : a = j
    · simpa only [Matrix.updateRow_apply, ha, if_true] using
        (differentiableAt_const (row b) : DifferentiableAt ℝ (fun _ : Mat => row b) G)
    · simpa only [Matrix.updateRow_apply, ha, if_false] using differentiableAt_matrixEntry G a b
  have hd := differentiableAt_matrixDet G
  have ha : DifferentiableAt ℝ (fun A : Mat => A.adjugate i j) G := by
    simpa only [Function.comp_apply, Matrix.adjugate_apply, row] using
      (differentiableAt_matrixDet (G.updateRow j row)).comp G hu
  simpa only [inverseMatrix, matrixInverse, Matrix.inv_def, Ring.inverse_eq_inv',
    Matrix.smul_apply, smul_eq_mul, Pi.inv_apply] using (hd.inv hG).mul ha

private theorem differentiableAt_metricDensity (G : Mat) (hG : Matrix.det G ≠ 0) :
    DifferentiableAt ℝ metricDensity G :=
  ((differentiableAt_matrixDet G).abs hG).sqrt (abs_ne_zero.mpr hG)

private theorem fderiv_eq_deriv_along_affine_metric (F : Mat → ℝ) (G H : Mat)
    (hF : DifferentiableAt ℝ F G) :
    fderiv ℝ F G H = deriv (fun t : ℝ => F (G + t • H)) 0 := by
  have hd : HasDerivAt (fun t : ℝ => t • H) H 0 := by
    simpa only [id_eq, one_smul] using (hasDerivAt_id (0 : ℝ)).smul_const H
  have hline := hd.const_add G
  have hcomp := hF.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline
    (by simp only [zero_smul, add_zero])
  exact hcomp.deriv.symm

private theorem coordinatePartial_comp_metric (F : Mat → ℝ) (g : E → Mat) (x : E) (a : Index)
    (hF : DifferentiableAt ℝ F (g x)) (hg : DifferentiableComponentsAt g x) :
    coordinatePartial (fun y => F (g y)) x a = fderiv ℝ F (g x) (coordinateJet g x a) := by
  have hgd : DifferentiableAt ℝ g x :=
    differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => hg i j
  have hJ : fderiv ℝ g x (EuclideanSpace.single a 1) = coordinateJet g x a := by
    funext i j
    have hp := hasFDerivAt_pi'.mp hgd.hasFDerivAt i
    have hq := hasFDerivAt_pi'.mp hp j
    exact (DFunLike.congr_fun hq.fderiv (EuclideanSpace.single a 1)).symm
  change fderiv ℝ (F ∘ g) x (EuclideanSpace.single a 1) = _
  rw [(hF.hasFDerivAt.comp x hgd.hasFDerivAt).fderiv]
  exact congrArg (fderiv ℝ F (g x)) hJ

private theorem christoffel_matrix_metric_compatible (G : Mat) (J : Jet)
    (hG : IsSymmetricTensor G) (hJ : ∀ a, IsSymmetricTensor (J a)) (hn : Matrix.det G ≠ 0) (a : Index) :
    let K := connectionMatrix (christoffel (inverseMatrix G) J) a
    Kᵀ * G + G * K = J a := by
  have hi : (G * inverseMatrix G : Mat) = 1 := compose_matrixInverse G hn
  have hc (b c : Index) :
      (∑ e, G b e * inverseMatrix G e c) = if b = c then 1 else 0 := by
    simpa only [Matrix.mul_apply, Matrix.one_apply] using congrArg (fun B : Mat => B b c) hi
  exact (matrix_metric_compatible_iff G J _).mp
    (christoffel_metric_compatible G (inverseMatrix G) J hG hJ hc) a

private theorem inverseVariation_eq_christoffel_comp (G : Mat) (J : Jet)
    (hG : IsSymmetricTensor G) (hJ : ∀ a, IsSymmetricTensor (J a)) (hn : Matrix.det G ≠ 0) (a : Index) :
    let B := inverseMatrix G
    let K := connectionMatrix (christoffel B J) a
    inverseVariation G (J a) = -(B * Kᵀ + K * B) := by
  intro B K
  have hGinv : (G * B : Mat) = 1 := compose_matrixInverse G hn
  have hInvG : (B * G : Mat) = 1 := matrixInverse_compose G hn
  have hc : Kᵀ * G + G * K = J a := christoffel_matrix_metric_compatible G J hG hJ hn a
  change -(B * J a * B) = _
  congr 1
  calc
    B * J a * B = B * (Kᵀ * G + G * K) * B := by rw [hc]
    _ = (B * Kᵀ) * (G * B) + (B * G) * (K * B) := by noncomm_ring
    _ = _ := by rw [hGinv, hInvG, Matrix.mul_one, Matrix.one_mul]

private theorem traceVariation_eq_two_connectionTrace (G : Mat) (J : Jet)
    (hG : IsSymmetricTensor G) (hJ : ∀ a, IsSymmetricTensor (J a)) (hn : Matrix.det G ≠ 0) (a : Index) :
    traceVariation G (J a) = 2 * connectionTrace (christoffel (inverseMatrix G) J) a := by
  let B := inverseMatrix G
  let K := connectionMatrix (christoffel B J) a
  have hGinv : (G * B : Mat) = 1 := compose_matrixInverse G hn
  have hInvG : (B * G : Mat) = 1 := matrixInverse_compose G hn
  have hc : Kᵀ * G + G * K = J a := christoffel_matrix_metric_compatible G J hG hJ hn a
  change Matrix.trace (J a * B) = 2 * Matrix.trace K
  rw [← hc, Matrix.add_mul, Matrix.trace_add, Matrix.mul_assoc Kᵀ G B, Matrix.mul_assoc G K B,
    Matrix.trace_mul_comm G (K * B), Matrix.mul_assoc K B G, hGinv, hInvG, Matrix.mul_one, Matrix.mul_one,
    Matrix.trace_transpose]
  ring

/-- The true coordinate derivative of the inverse metric in terms of the
computed Christoffel symbols. -/
theorem coordinatePartial_inverseMatrix (g : E → Mat) (x : E)
    (hg : DifferentiableComponentsAt g x) (hG : IsSymmetricTensor (g x))
    (hJ : ∀ d, IsSymmetricTensor (coordinateJet g x d)) (hn : Matrix.det (g x) ≠ 0) (a b c : Index) :
    let B := inverseMatrix (g x)
    let Γ := coordinateConnectionFromMetric g x
    coordinatePartial (fun y => inverseMatrix (g y) b c) x a =
      -∑ e, (B b e * Γ c a e + Γ b a e * B e c) := by
  intro B Γ
  have hF := differentiableAt_inverseMatrixEntry (g x) hn b c
  rw [coordinatePartial_comp_metric _ g x a hF hg,
    fderiv_eq_deriv_along_affine_metric _ _ _ hF,
    (hasDerivAt_inverseMatrix_entry_path (g x) (coordinateJet g x a) hn b c).deriv]
  have h := congrArg (fun A : Mat => A b c)
    (inverseVariation_eq_christoffel_comp (g x) (coordinateJet g x) hG hJ hn a)
  simpa only [Matrix.neg_apply, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix,
    ← Finset.sum_add_distrib] using h

/-- The true spatial derivative of the determinant volume density equals
the volume density times the trace of the computed connection. -/
theorem coordinatePartial_metricDensity (g : E → Mat) (x : E)
    (hg : DifferentiableComponentsAt g x) (hG : IsSymmetricTensor (g x))
    (hJ : ∀ d, IsSymmetricTensor (coordinateJet g x d)) (hn : Matrix.det (g x) ≠ 0) (a : Index) :
    coordinatePartial (fun y => metricDensity (g y)) x a =
      metricDensity (g x) * connectionTrace (coordinateConnectionFromMetric g x) a := by
  have hF := differentiableAt_metricDensity (g x) hn
  rw [coordinatePartial_comp_metric _ g x a hF hg,
    fderiv_eq_deriv_along_affine_metric _ _ _ hF,
    (hasDerivAt_metricDensity_path (g x) (coordinateJet g x a) hn).deriv,
    traceVariation_eq_two_connectionTrace (g x) (coordinateJet g x) hG hJ hn a]
  change _ = metricDensity (g x) *
    connectionTrace (christoffel (inverseMatrix (g x)) (coordinateJet g x)) a
  ring

end Burnett.V02.EinsteinHilbert
