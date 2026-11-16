import Mathlib.Analysis.Matrix.Order

/-!
# Positive matrix densities and a system kernel

This finite-dimensional algebraic bridge is one input to F05 localization.
It does not construct a microlocal measure or prove an almost-everywhere
localization statement. The density may be singular.
-/

noncomputable section

namespace Burnett.Microlocal.PositiveKernel

open Matrix
open scoped ComplexOrder

variable {𝕜 n m : Type*} [RCLike 𝕜] [Fintype n]

/-- If the compression of a positive density by a system vanishes, the
density annihilates the adjoint system. No invertibility is required. -/
theorem mul_conjTranspose_eq_zero_of_compression_eq_zero
    {M : Matrix n n 𝕜} (hM : M.PosSemidef) (A : Matrix m n 𝕜)
    (h : A * M * Aᴴ = 0) : M * Aᴴ = 0 := by
  have hv (i : m) : M *ᵥ star (A i) = 0 := by
    apply (hM.dotProduct_mulVec_zero_iff (star (A i))).mp
    rw [star_star, Matrix.dotProduct_mulVec]
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, dotProduct]
      using congrArg (fun B : Matrix m m 𝕜 => B i i) h
  ext j i
  exact congrFun (hv i) j

/-- A positive density with zero system compression has its image in the
system kernel, expressed as the exact matrix equation `A * M = 0`. -/
theorem mul_eq_zero_of_compression_eq_zero
    {M : Matrix n n 𝕜} (hM : M.PosSemidef) (A : Matrix m n 𝕜)
    (h : A * M * Aᴴ = 0) : A * M = 0 := by
  have h' := congrArg Matrix.conjTranspose
    (mul_conjTranspose_eq_zero_of_compression_eq_zero hM A h)
  simpa only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    hM.isHermitian.eq, Matrix.conjTranspose_zero] using h'

/-- Vector form of the system-kernel inclusion. -/
theorem mulVec_eq_zero_of_compression_eq_zero
    {M : Matrix n n 𝕜} (hM : M.PosSemidef) (A : Matrix m n 𝕜)
    (h : A * M * Aᴴ = 0) (x : n → 𝕜) : A *ᵥ (M *ᵥ x) = 0 := by
  rw [Matrix.mulVec_mulVec, mul_eq_zero_of_compression_eq_zero hM A h,
    Matrix.zero_mulVec]

/-- The actual range of the density's linear map lies in the actual kernel
of the system's linear map. -/
theorem range_le_ker_of_compression_eq_zero
    {M : Matrix n n 𝕜} (hM : M.PosSemidef) (A : Matrix m n 𝕜)
    (h : A * M * Aᴴ = 0) :
    LinearMap.range M.mulVecLin ≤ LinearMap.ker A.mulVecLin := by
  rintro y ⟨x, rfl⟩
  change A *ᵥ (M *ᵥ x) = 0
  exact mulVec_eq_zero_of_compression_eq_zero hM A h x

end Burnett.Microlocal.PositiveKernel
