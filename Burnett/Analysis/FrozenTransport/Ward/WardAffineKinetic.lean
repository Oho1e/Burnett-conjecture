import Burnett.Analysis.FrozenTransport.Ward.WardAffineConnectionCross
import Burnett.Geometry.TensorCoordinateChange

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 11000000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol Burnett.Geometry.ConnectionCoordinateChange Burnett.Geometry.TensorCoordinateChange
open Burnett.Geometry.ConnectionDifference
open scoped Matrix

/-- Pull the first metric jet back by a genuinely constant matrix. -/
def wardAffineJet (A : Mat) (X : Jet) : Jet :=
  fun b => Aᵀ * (∑ p : Fin 4, A p b • X p) * A

private theorem wardAffineJet_eq_transformedJet (A G : Mat) (X : Jet) :
    transformedJet A G X 0 = wardAffineJet A X := by
  funext b
  change transformedMetricDerivative A G (∑ p, A p b • X p) (connectionMatrix 0 b) = _
  have h0 : connectionMatrix 0 b = 0 := rfl
  simp only [transformedMetricDerivative, h0, transpose_zero, zero_mul, zero_add, mul_zero, add_zero, wardAffineJet]

private theorem wardChristoffel_affine (A G : Mat) (hA : IsUnit A) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (X : Jet) (hXsym : ∀ d, IsSymmetricTensor (X d)) :
    christoffel (inverseMatrix (pullbackMetric G A)) (wardAffineJet A X) =
      wardAffineConnection A (christoffel (inverseMatrix G) X) := by
  have h := transformed_christoffel A G X 0 hA hG hGsym hXsym (fun _ _ _ => rfl)
  rw [wardAffineJet_eq_transformedJet] at h
  exact h.symm

private theorem wardUpperContract_affine (A B B' : Mat) (hB : A * B' * Aᵀ = B) (R : Mat) :
    (∑ b : Fin 4, ∑ c : Fin 4, B' b c * (∑ p : Fin 4, ∑ q : Fin 4, A p b * A q c * R p q)) =
      ∑ p : Fin 4, ∑ q : Fin 4, B p q * R p q := by
  let f (b c p q : Fin 4) := B' b c * A p b * A q c * R p q
  have hf (p q : Fin 4) : (∑ b, ∑ c, f b c p q) = B p q * R p q := by
    rw [← hB]
    simp only [Matrix.mul_apply, transpose_apply, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intro c _
    unfold f
    ring
  calc
    _ = ∑ b, ∑ c, ∑ p, ∑ q, f b c p q := by
      simp only [Finset.mul_sum, f, mul_assoc]
    _ = ∑ b, ∑ p, ∑ c, ∑ q, f b c p q := by
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ b, ∑ c, ∑ q, f b c p q := by rw [Finset.sum_comm]
    _ = ∑ p, ∑ b, ∑ q, ∑ c, f b c p q := by
      apply Finset.sum_congr rfl
      intro p _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.sum_comm]
    _ = ∑ p, ∑ q, ∑ b, ∑ c, f b c p q := by
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_comm]
    _ = _ := by simp only [hf]

theorem gammaCross_affine (A G : Mat) (hA : IsUnit A) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (X Y : Jet) (hXsym : ∀ d, IsSymmetricTensor (X d)) (hYsym : ∀ d, IsSymmetricTensor (Y d)) :
    gammaCross (inverseMatrix (pullbackMetric G A)) (wardAffineJet A X) (wardAffineJet A Y) =
      gammaCross (inverseMatrix G) X Y := by
  let C := christoffel (inverseMatrix G) X
  let D := christoffel (inverseMatrix G) Y
  let R : Mat := fun p q => connectionCross C D p q
  have hC : ∀ a b c, C a b c = C a c b := christoffel_torsion_free _ _ hXsym
  unfold gammaCross
  rw [wardChristoffel_affine A G hA hG hGsym X hXsym, wardChristoffel_affine A G hA hG hGsym Y hYsym]
  change (∑ b, ∑ c, inverseMatrix (pullbackMetric G A) b c *
    connectionCross (wardAffineConnection A C) (wardAffineConnection A D) b c) =
      ∑ b, ∑ c, inverseMatrix G b c * connectionCross C D b c
  simp_rw [connectionCross_affine_covariance A hA C D hC]
  exact wardUpperContract_affine A (inverseMatrix G) (inverseMatrix (pullbackMetric G A))
    (inverse_pullback_cancel G A hA) R

theorem metricDensity_affine (A G : Mat) : metricDensity (pullbackMetric G A) = |A.det| * metricDensity G := by
  simp only [metricDensity, pullbackMetric, Matrix.det_mul, Matrix.det_transpose, abs_mul]
  have h : |A.det| * |G.det| * |A.det| = |A.det|^2 * |G.det| := by ring
  rw [h, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]

/-- Affine covariance of the actual frozen quadratic action coefficient,
including the absolute Jacobian factor that multiplies the density. -/
theorem metricKineticCoefficient_affine (A G : Mat) (hA : IsUnit A) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (X Y : Jet)
    (hXsym : ∀ d, IsSymmetricTensor (X d)) (hYsym : ∀ d, IsSymmetricTensor (Y d)) :
    metricKineticCoefficient (pullbackMetric G A) (wardAffineJet A X) (wardAffineJet A Y) =
      |A.det| * metricKineticCoefficient G X Y := by
  simp only [metricKineticCoefficient, kineticCoefficient_eq_cross, metricDensity_affine,
    gammaCross_affine A G hA hG hGsym X Y hXsym hYsym,
    gammaCross_affine A G hA hG hGsym Y X hYsym hXsym, mul_assoc]

end Burnett.Analysis.TransportWardSymbol
