import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.InnerProductSpace.Basic

open Matrix

/-! Actual Gram energies, their induced Hilbert norm, and inverse-diagonal coordinate bounds. -/

namespace Burnett.Geometry.GramCoordinateBound

variable {n : Type*} [Fintype n]

/-- The actual Gram quadratic energy, using the given component matrix. -/
def gramEnergy (G : Matrix n n ℝ) (x : n → ℝ) : ℝ := x ⬝ᵥ (G *ᵥ x)

/-- The Hilbert norm supplied by a positive Gram matrix, written explicitly. -/
noncomputable def gramNorm (G : Matrix n n ℝ) (x : n → ℝ) : ℝ :=
  Real.sqrt (gramEnergy G x)

theorem gramEnergy_nonneg (G : Matrix n n ℝ) (hG : G.PosSemidef) (x : n → ℝ) :
    0 ≤ gramEnergy G x := by
  simpa only [gramEnergy, star_trivial] using hG.2 x

theorem gramNorm_nonneg (G : Matrix n n ℝ) (x : n → ℝ) : 0 ≤ gramNorm G x :=
  Real.sqrt_nonneg _

theorem gramNorm_sq (G : Matrix n n ℝ) (hG : G.PosSemidef) (x : n → ℝ) :
    gramNorm G x ^ 2 = gramEnergy G x :=
  Real.sq_sqrt (gramEnergy_nonneg G hG x)

theorem gramNorm_eq_ofMatrix_norm (G : Matrix n n ℝ) (hG : G.PosDef) (x : n → ℝ) :
    gramNorm G x = @Norm.norm (n → ℝ) (Matrix.NormedAddCommGroup.ofMatrix hG).toNorm x := by
  change Real.sqrt (x ⬝ᵥ (G *ᵥ x)) = Real.sqrt ((G *ᵥ x) ⬝ᵥ star x)
  simp only [star_trivial, dotProduct_comm]

variable [DecidableEq n]

theorem inverse_diagonal_nonneg (G : Matrix n n ℝ) (hG : G.PosDef) (i : n) :
    0 ≤ G⁻¹ i i := by
  have h := hG.inv.posSemidef.2 (Pi.single i 1)
  simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct, one_mul,
    Matrix.col_apply] using h

/-- Cauchy--Schwarz for the constructed Gram inner product controls each coordinate. -/
theorem coordinate_sq_le_inverse_diagonal
    (G : Matrix n n ℝ) (hG : G.PosDef) (x : n → ℝ) (i : n) :
    (x i)^2 ≤ G⁻¹ i i * gramEnergy G x := by
  let y : n → ℝ := G⁻¹ *ᵥ Pi.single i 1
  have hy : G *ᵥ y = Pi.single i 1 := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr (ne_of_gt hG.det_pos)),
      Matrix.one_mulVec]
  have hc := @real_inner_mul_inner_self_le (n → ℝ)
    (Matrix.NormedAddCommGroup.ofMatrix hG).toSeminormedAddCommGroup
    (Matrix.InnerProductSpace.ofMatrix hG) x y
  change ((G *ᵥ y) ⬝ᵥ x) * ((G *ᵥ y) ⬝ᵥ x) ≤
    ((G *ᵥ x) ⬝ᵥ x) * ((G *ᵥ y) ⬝ᵥ y) at hc
  rw [hy] at hc
  simp only [single_dotProduct, one_mul] at hc
  have hiy : y i = G⁻¹ i i := by
    simp only [y, Matrix.mulVec_single_one, Matrix.col_apply]
  rw [hiy] at hc
  simpa only [gramEnergy, pow_two, dotProduct_comm, mul_comm] using hc

theorem abs_apply_le_sqrt_inverse_diagonal_mul_gramNorm
    (G : Matrix n n ℝ) (hG : G.PosDef) (x : n → ℝ) (i : n) :
    |x i| ≤ Real.sqrt (G⁻¹ i i) * gramNorm G x := by
  calc
    |x i| = Real.sqrt ((x i)^2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (G⁻¹ i i * gramEnergy G x) :=
      Real.sqrt_le_sqrt (coordinate_sq_le_inverse_diagonal G hG x i)
    _ = Real.sqrt (G⁻¹ i i) * gramNorm G x :=
      Real.sqrt_mul (inverse_diagonal_nonneg G hG i) _

theorem norm_apply_le_sqrt_inverse_diagonal_mul_gramNorm
    (G : Matrix n n ℝ) (hG : G.PosDef) (x : n → ℝ) (i : n) :
    ‖x i‖ ≤ Real.sqrt (G⁻¹ i i) * gramNorm G x := by
  simpa only [Real.norm_eq_abs] using
    abs_apply_le_sqrt_inverse_diagonal_mul_gramNorm G hG x i

end Burnett.Geometry.GramCoordinateBound

