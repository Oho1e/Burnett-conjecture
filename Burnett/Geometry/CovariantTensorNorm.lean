import Burnett.Geometry.GramCoordinateBound
import Burnett.Geometry.ConnectionDifference
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.Vec

/-!
# Physical norms for covariant two- and three-tensors

R is the positive definite covariant auxiliary metric matrix. Its actual
matrix inverse contracts every covariant index. The induced Gram matrices
are proved positive definite, and their inverse diagonals use R, not R⁻¹.
All coordinate norms on the tensor arrays remain the existing Pi sup norms.
-/

noncomputable section

namespace Burnett.Geometry.CovariantTensorNorm

open Matrix
open scoped BigOperators Kronecker
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.GramCoordinateBound

theorem isUnit_kronecker_real {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (hA : IsUnit A) (hB : IsUnit B) : IsUnit (A ⊗ₖ B) := by
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  rw [Matrix.det_kronecker]
  exact (((Matrix.isUnit_iff_isUnit_det _).mp hA).pow _).mul
    (((Matrix.isUnit_iff_isUnit_det _).mp hB).pow _)

theorem posDef_kronecker {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m ℝ) (B : Matrix n n ℝ)
    (hA : A.PosDef) (hB : B.PosDef) : (A ⊗ₖ B).PosDef := by
  obtain ⟨C, hC, rfl⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hA
  obtain ⟨D, hD, rfl⟩ := Matrix.posDef_iff_eq_conjTranspose_mul_self.mp hB
  rw [Matrix.mul_kronecker_mul, ← Matrix.conjTranspose_kronecker]
  exact Matrix.PosDef.conjTranspose_mul_self _
    (Matrix.mulVec_injective_of_isUnit (isUnit_kronecker_real C D hC hD))

/-- Explicit row-major flattening. Mathlib's `Matrix.vec` reverses the pair. -/
def flatten2 (T : Tensor2) : Index × Index → ℝ := fun ij => T ij.1 ij.2

def flatten3 (T : FirstJet) : (Index × Index) × Index → ℝ :=
  fun ijk => T ijk.1.1 ijk.1.2 ijk.2

theorem flatten2_eq_vec_transpose (T : Tensor2) : flatten2 T = Matrix.vec Tᵀ := rfl

theorem flatten3_eq_vec_transpose (T : FirstJet) :
    flatten3 T = Matrix.vec (fun ij k => T ij.1 ij.2 k)ᵀ := rfl

def gram2 (R : Matrix Index Index ℝ) : Matrix (Index × Index) (Index × Index) ℝ :=
  (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R) ⊗ₖ
    (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R)

def gram3 (R : Matrix Index Index ℝ) :
    Matrix ((Index × Index) × Index) ((Index × Index) × Index) ℝ :=
  gram2 R ⊗ₖ (@Inv.inv (Matrix Index Index ℝ) Matrix.inv R)

theorem gram2_posDef (R : Matrix Index Index ℝ) (hR : R.PosDef) : (gram2 R).PosDef :=
  posDef_kronecker _ _ hR.inv hR.inv

theorem gram3_posDef (R : Matrix Index Index ℝ) (hR : R.PosDef) : (gram3 R).PosDef :=
  posDef_kronecker _ _ (gram2_posDef R hR) hR.inv

theorem gram2_inverse (R : Matrix Index Index ℝ) (hR : R.PosDef) :
    (gram2 R)⁻¹ = R ⊗ₖ R := by
  have hi := Matrix.nonsing_inv_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  unfold gram2
  rw [Matrix.inv_kronecker, hi]

theorem gram3_inverse (R : Matrix Index Index ℝ) (hR : R.PosDef) :
    (gram3 R)⁻¹ = (R ⊗ₖ R) ⊗ₖ R := by
  have hi := Matrix.nonsing_inv_nonsing_inv R ((Matrix.isUnit_iff_isUnit_det R).mp hR.isUnit)
  unfold gram3
  rw [Matrix.inv_kronecker, gram2_inverse R hR, hi]

/-- Full contraction of a genuine covariant two-tensor by the inverse metric. -/
def energy2 (R : Matrix Index Index ℝ) (T : Tensor2) : ℝ :=
  let S := @Inv.inv (Matrix Index Index ℝ) Matrix.inv R
  ∑ i, ∑ j, ∑ a, ∑ b, S i a * S j b * T i j * T a b

/-- The first index may be a covariant derivative index; it is contracted by
the same inverse auxiliary metric as the other two covariant indices. -/
def energy3 (R : Matrix Index Index ℝ) (T : FirstJet) : ℝ :=
  let S := @Inv.inv (Matrix Index Index ℝ) Matrix.inv R
  ∑ i, ∑ j, ∑ k, ∑ a, ∑ b, ∑ c,
    S i a * S j b * S k c * T i j k * T a b c

def norm2 (R : Matrix Index Index ℝ) (T : Tensor2) : ℝ := Real.sqrt (energy2 R T)

def norm3 (R : Matrix Index Index ℝ) (T : FirstJet) : ℝ := Real.sqrt (energy3 R T)

theorem energy2_eq_gramEnergy (R : Matrix Index Index ℝ) (T : Tensor2) :
    energy2 R T = gramEnergy (gram2 R) (flatten2 T) := by
  simp only [energy2, gramEnergy, flatten2, gram2, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

theorem energy3_eq_gramEnergy (R : Matrix Index Index ℝ) (T : FirstJet) :
    energy3 R T = gramEnergy (gram3 R) (flatten3 T) := by
  simp only [energy3, gramEnergy, flatten3, gram3, gram2, Matrix.mulVec, dotProduct,
    Matrix.kronecker_apply, Fintype.sum_prod_type]
  simp_rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr rfl (fun c _ => ?_)
  ring

theorem energy2_nonneg (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : Tensor2) :
    0 ≤ energy2 R T := by
  rw [energy2_eq_gramEnergy]
  exact gramEnergy_nonneg _ (gram2_posDef R hR).posSemidef _

theorem energy3_nonneg (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : FirstJet) :
    0 ≤ energy3 R T := by
  rw [energy3_eq_gramEnergy]
  exact gramEnergy_nonneg _ (gram3_posDef R hR).posSemidef _

theorem norm2_eq_gramNorm (R : Matrix Index Index ℝ) (T : Tensor2) :
    norm2 R T = gramNorm (gram2 R) (flatten2 T) := by
  simp only [norm2, gramNorm, energy2_eq_gramEnergy]

theorem norm3_eq_gramNorm (R : Matrix Index Index ℝ) (T : FirstJet) :
    norm3 R T = gramNorm (gram3 R) (flatten3 T) := by
  simp only [norm3, gramNorm, energy3_eq_gramEnergy]

theorem norm2_eq_ofMatrix_norm (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : Tensor2) :
    norm2 R T = @Norm.norm ((Index × Index) → ℝ)
      (Matrix.NormedAddCommGroup.ofMatrix (gram2_posDef R hR)).toNorm (flatten2 T) := by
  rw [norm2_eq_gramNorm]
  exact gramNorm_eq_ofMatrix_norm _ (gram2_posDef R hR) _

theorem norm3_eq_ofMatrix_norm (R : Matrix Index Index ℝ) (hR : R.PosDef) (T : FirstJet) :
    norm3 R T = @Norm.norm (((Index × Index) × Index) → ℝ)
      (Matrix.NormedAddCommGroup.ofMatrix (gram3_posDef R hR)).toNorm (flatten3 T) := by
  rw [norm3_eq_gramNorm]
  exact gramNorm_eq_ofMatrix_norm _ (gram3_posDef R hR) _

theorem abs_entry_le_norm2 (R : Matrix Index Index ℝ) (hR : R.PosDef)
    (T : Tensor2) (i j : Index) : |T i j| ≤ Real.sqrt (R i i * R j j) * norm2 R T := by
  have h := abs_apply_le_sqrt_inverse_diagonal_mul_gramNorm
    (gram2 R) (gram2_posDef R hR) (flatten2 T) (i, j)
  rw [gram2_inverse R hR] at h
  simpa only [Matrix.kronecker_apply, flatten2, ← norm2_eq_gramNorm] using h

theorem abs_entry_le_norm3 (R : Matrix Index Index ℝ) (hR : R.PosDef)
    (T : FirstJet) (i j k : Index) :
    |T i j k| ≤ Real.sqrt (R i i * R j j * R k k) * norm3 R T := by
  have h := abs_apply_le_sqrt_inverse_diagonal_mul_gramNorm
    (gram3 R) (gram3_posDef R hR) (flatten3 T) ((i, j), k)
  rw [gram3_inverse R hR] at h
  simpa only [Matrix.kronecker_apply, flatten3, ← norm3_eq_gramNorm] using h

theorem diagonal_nonneg (R : Matrix Index Index ℝ) (hR : R.PosDef) (i : Index) :
    0 ≤ R i i := by
  have h := hR.posSemidef.2 (Pi.single i 1)
  simpa only [star_trivial, Matrix.mulVec_single_one, single_dotProduct, one_mul,
    Matrix.col_apply] using h

theorem coordinate_sup_le_norm2 (R : Matrix Index Index ℝ) (hR : R.PosDef)
    (T : Tensor2) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ i, R i i ≤ M) :
    ‖T‖ ≤ Real.sqrt (M ^ 2) * norm2 R T := by
  have hnon : 0 ≤ Real.sqrt (M ^ 2) * norm2 R T :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hnon).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hnon).mpr
  intro j
  rw [Real.norm_eq_abs]
  have hp := mul_le_mul (hd i) (hd j) (diagonal_nonneg R hR j) hM
  have hprod : R i i * R j j ≤ M ^ 2 := by nlinarith
  exact (abs_entry_le_norm2 R hR T i j).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hprod) (Real.sqrt_nonneg _))

/-- Pointwise Pi sup control from covariant metric diagonal bounds. -/
theorem coordinate_sup_le_norm3 (R : Matrix Index Index ℝ) (hR : R.PosDef)
    (T : FirstJet) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ i, R i i ≤ M) :
    ‖T‖ ≤ Real.sqrt (M ^ 3) * norm3 R T := by
  have hnon : 0 ≤ Real.sqrt (M ^ 3) * norm3 R T :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  apply (pi_norm_le_iff_of_nonneg hnon).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg hnon).mpr
  intro j
  apply (pi_norm_le_iff_of_nonneg hnon).mpr
  intro k
  rw [Real.norm_eq_abs]
  have hp := mul_le_mul (hd i) (hd j) (diagonal_nonneg R hR j) hM
  have hp' := mul_le_mul hp (hd k) (diagonal_nonneg R hR k) (mul_nonneg hM hM)
  have hprod : R i i * R j j * R k k ≤ M ^ 3 := by nlinarith
  exact (abs_entry_le_norm3 R hR T i j k).trans
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hprod) (Real.sqrt_nonneg _))

/-- The compact-set comparison constant is derived from the continuous
covariant R diagonals. It is not a new assumed norm-equivalence constant. -/
theorem exists_uniform_norm3_control {X : Type*} [TopologicalSpace X]
    (R : X → Matrix Index Index ℝ) (K : Set X) (hK : IsCompact K)
    (hc : ∀ i, ContinuousOn (fun x => R x i i) K)
    (hR : ∀ x ∈ K, (R x).PosDef) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : FirstJet, ‖T‖ ≤ C * norm3 (R x) T := by
  have hdiag : ContinuousOn (fun x i => R x i i) K := continuousOn_pi.mpr hc
  obtain ⟨M, hM, hb⟩ := (hK.image_of_continuousOn hdiag).isBounded.exists_pos_norm_le
  refine ⟨Real.sqrt (M ^ 3), Real.sqrt_pos.mpr (pow_pos hM _), ?_⟩
  intro x hx T
  apply coordinate_sup_le_norm3 (R x) (hR x hx) T hM.le
  intro i
  have hi : |R x i i| ≤ M := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (fun i => R x i i) i).trans (hb _ (Set.mem_image_of_mem _ hx))
  exact (le_abs_self _).trans hi

theorem exists_uniform_norm2_control {X : Type*} [TopologicalSpace X]
    (R : X → Matrix Index Index ℝ) (K : Set X) (hK : IsCompact K)
    (hc : ∀ i, ContinuousOn (fun x => R x i i) K)
    (hR : ∀ x ∈ K, (R x).PosDef) :
    ∃ C > 0, ∀ x ∈ K, ∀ T : Tensor2, ‖T‖ ≤ C * norm2 (R x) T := by
  have hdiag : ContinuousOn (fun x i => R x i i) K := continuousOn_pi.mpr hc
  obtain ⟨M, hM, hb⟩ := (hK.image_of_continuousOn hdiag).isBounded.exists_pos_norm_le
  refine ⟨Real.sqrt (M ^ 2), Real.sqrt_pos.mpr (pow_pos hM _), ?_⟩
  intro x hx T
  apply coordinate_sup_le_norm2 (R x) (hR x hx) T hM.le
  intro i
  have hi : |R x i i| ≤ M := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm (fun i => R x i i) i).trans (hb _ (Set.mem_image_of_mem _ hx))
  exact (le_abs_self _).trans hi

end Burnett.Geometry.CovariantTensorNorm
