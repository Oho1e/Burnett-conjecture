import Burnett.Geometry.CovariantTensorNorm

/-! Actual pullbacks of covariant tensors and invariance of the physical
contraction norms. A maps new coordinate vectors to old coordinate vectors.
No operator norm on a curried Hom type is identified with a tensor norm. -/

noncomputable section

namespace Burnett.Geometry.TensorCoordinateChange

set_option maxRecDepth 4096

open Matrix
open scoped Kronecker BigOperators
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.GramCoordinateBound
open Burnett.Geometry.CovariantTensorNorm

def pullbackMetric (R A : Matrix Index Index ℝ) : Matrix Index Index ℝ := Aᵀ * R * A

def pullback2 (A : Matrix Index Index ℝ) (T : Tensor2) : Tensor2 :=
  fun i j => ((Aᵀ ⊗ₖ Aᵀ) *ᵥ flatten2 T) (i, j)

def pullback3 (A : Matrix Index Index ℝ) (T : FirstJet) : FirstJet :=
  fun i j k => (((Aᵀ ⊗ₖ Aᵀ) ⊗ₖ Aᵀ) *ᵥ flatten3 T) ((i, j), k)

theorem flatten2_pullback (A : Matrix Index Index ℝ) (T : Tensor2) :
    flatten2 (pullback2 A T) = (Aᵀ ⊗ₖ Aᵀ) *ᵥ flatten2 T := rfl

theorem flatten3_pullback (A : Matrix Index Index ℝ) (T : FirstJet) :
    flatten3 (pullback3 A T) = ((Aᵀ ⊗ₖ Aᵀ) ⊗ₖ Aᵀ) *ᵥ flatten3 T := rfl

theorem pullback2_apply (A : Matrix Index Index ℝ) (T : Tensor2) (i j : Index) :
    pullback2 A T i j = ∑ a, ∑ b, A a i * A b j * T a b := by
  simp only [pullback2, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.transpose_apply, flatten2, Fintype.sum_prod_type]

theorem pullback3_apply (A : Matrix Index Index ℝ) (T : FirstJet) (i j k : Index) :
    pullback3 A T i j k = ∑ a, ∑ b, ∑ c, A a i * A b j * A c k * T a b c := by
  simp only [pullback3, Matrix.mulVec, dotProduct, Matrix.kronecker_apply,
    Matrix.transpose_apply, flatten3, Fintype.sum_prod_type]

theorem pullbackMetric_posDef (R A : Matrix Index Index ℝ)
    (hR : R.PosDef) (hA : IsUnit A) : (pullbackMetric R A).PosDef := by
  simpa only [pullbackMetric, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hR.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hA)

theorem inverse_pullback_cancel (R A : Matrix Index Index ℝ) (hA : IsUnit A) :
    A * (pullbackMetric R A)⁻¹ * Aᵀ = R⁻¹ := by
  have ha : IsUnit A.det := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hat : IsUnit Aᵀ.det := by simpa only [Matrix.det_transpose] using ha
  simp only [pullbackMetric, Matrix.mul_inv_rev]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv A ha,
    Matrix.one_mul, Matrix.mul_assoc, Matrix.nonsing_inv_mul Aᵀ hat, Matrix.mul_one]

theorem gramEnergy_congr {n : Type*} [Fintype n]
    (G A : Matrix n n ℝ) (x : n → ℝ) :
    gramEnergy (Aᵀ * G * A) x = gramEnergy G (A *ᵥ x) := by
  unfold gramEnergy
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem gram2_pullback_cancel (R A : Matrix Index Index ℝ) (hA : IsUnit A) :
    (Aᵀ ⊗ₖ Aᵀ)ᵀ * gram2 (pullbackMetric R A) * (Aᵀ ⊗ₖ Aᵀ) = gram2 R := by
  simp only [← Matrix.kroneckerMap_transpose, Matrix.transpose_transpose, gram2,
    ← Matrix.mul_kronecker_mul, inverse_pullback_cancel R A hA]

theorem gram3_pullback_cancel (R A : Matrix Index Index ℝ) (hA : IsUnit A) :
    ((Aᵀ ⊗ₖ Aᵀ) ⊗ₖ Aᵀ)ᵀ * gram3 (pullbackMetric R A) *
      ((Aᵀ ⊗ₖ Aᵀ) ⊗ₖ Aᵀ) = gram3 R := by
  simp only [← Matrix.kroneckerMap_transpose, Matrix.transpose_transpose, gram3, gram2,
    ← Matrix.mul_kronecker_mul, inverse_pullback_cancel R A hA]

theorem energy2_pullback (R A : Matrix Index Index ℝ) (hA : IsUnit A) (T : Tensor2) :
    energy2 (pullbackMetric R A) (pullback2 A T) = energy2 R T := by
  rw [energy2_eq_gramEnergy, flatten2_pullback, ← gramEnergy_congr,
    gram2_pullback_cancel R A hA, ← energy2_eq_gramEnergy]

theorem energy3_pullback (R A : Matrix Index Index ℝ) (hA : IsUnit A) (T : FirstJet) :
    energy3 (pullbackMetric R A) (pullback3 A T) = energy3 R T := by
  rw [energy3_eq_gramEnergy, flatten3_pullback, ← gramEnergy_congr,
    gram3_pullback_cancel R A hA, ← energy3_eq_gramEnergy]

theorem norm2_pullback (R A : Matrix Index Index ℝ) (hA : IsUnit A) (T : Tensor2) :
    norm2 (pullbackMetric R A) (pullback2 A T) = norm2 R T := by
  simp only [norm2, energy2_pullback R A hA T]

theorem norm3_pullback (R A : Matrix Index Index ℝ) (hA : IsUnit A) (T : FirstJet) :
    norm3 (pullbackMetric R A) (pullback3 A T) = norm3 R T := by
  simp only [norm3, energy3_pullback R A hA T]

end Burnett.Geometry.TensorCoordinateChange
