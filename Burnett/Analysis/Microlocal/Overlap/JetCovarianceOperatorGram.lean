import Burnett.Analysis.Microlocal.CurlCovariance
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Covariance operators and adjoints with the auxiliary fiber Gram matrices. -/

set_option autoImplicit false
set_option maxHeartbeats 900000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Matrix Burnett.RicciSymbol
open Burnett.Microlocal.CurlDensity (JetSlot Pair gradientEmbedding)
open scoped Matrix Kronecker BigOperators

/-- Ordered tensor slots carry the same Gram expression even when its
positive inner product is restricted to the symmetric subspace. -/
theorem gradientEmbedding_conjTranspose_gram (ξ : Covector)
    (R : Matrix Index Index ℂ) (G : Matrix Pair Pair ℂ) :
    let J := gradientEmbedding ξ
    Jᴴ * (R ⊗ₖ G) * J =
      (∑ a : Index, ∑ b : Index, (ξ a : ℂ) * R a b * (ξ b : ℂ)) • G := by
  classical
  intro J
  have hFirst (p : Pair) (q : JetSlot) :
      (Jᴴ * (R ⊗ₖ G)) p q = (∑ a, (ξ a : ℂ) * R a q.1) * G p q.2 := by
    rw [Matrix.mul_apply, Fintype.sum_prod_type, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    rw [Finset.sum_eq_single p]
    · simp [J, Matrix.conjTranspose_apply, gradientEmbedding, Matrix.kroneckerMap, mul_assoc]
    · intro y _ hy
      simp [J, Matrix.conjTranspose_apply, gradientEmbedding, Ne.symm hy]
    · simp
  ext p q
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  calc
    _ = ∑ a : Index, ∑ b : Index, ((ξ b : ℂ) * R b a * (ξ a : ℂ)) * G p q := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_eq_single q]
      · simp only [hFirst, J, gradientEmbedding, if_true, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro b _
        ring
      · intro y _ hy
        simp [J, gradientEmbedding, Ne.symm hy]
      · simp
    _ = _ := by
      simp only [Matrix.smul_apply, smul_eq_mul, Finset.sum_mul]
      exact Finset.sum_comm

/-- In the actual auxiliary unit case jξ preserves the tensor Gram form. -/
theorem gradientEmbedding_isometry_gram (ξ : Covector)
    (R : Matrix Index Index ℂ) (G : Matrix Pair Pair ℂ)
    (hξ : (∑ a : Index, ∑ b : Index, (ξ a : ℂ) * R a b * (ξ b : ℂ)) = 1) :
    let J := gradientEmbedding ξ
    Jᴴ * (R ⊗ₖ G) * J = G := by
  intro J
  rw [gradientEmbedding_conjTranspose_gram, hξ, one_smul]

/-- Turn the actual covariance tensors into endomorphisms by multiplying
each on the right by its own fiber Gram. This gives the adjoint formula
for the same factorization. -/
theorem gradientCovariance_operator_factor (ξ : Covector) (C : Matrix Pair Pair ℂ)
    (G : Matrix Pair Pair ℂ) (hG : IsUnit G.det) (H : Matrix JetSlot JetSlot ℂ) :
    let J := gradientEmbedding ξ
    let adj := G⁻¹ * Jᴴ * H
    (J * C * Jᴴ) * H = J * (C * G) * adj := by
  intro J adj
  have hInv := Matrix.mul_nonsing_inv G hG
  calc
    _ = J * (C * ((1 : Matrix Pair Pair ℂ) * (Jᴴ * H))) := by simp [Matrix.mul_assoc]
    _ = _ := by rw [← hInv]; simp only [adj, Matrix.mul_assoc]

end Burnett.Microlocal.Overlap
