import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.P01

open Matrix
open scoped Matrix BigOperators

abbrev Covector := Fin 4 → ℝ
abbrev Components := Matrix (Fin 4) (Fin 4) ℝ

/-- The Euclidean projection perpendicular to the coordinate covector. -/
def directionProjection (ξ : Covector) : Components :=
  1 - (ξ ⬝ᵥ ξ)⁻¹ • vecMulVec ξ ξ

/-- The uncut matrix symbol `Π_E(ξ)` in the projected-source argument. -/
def euclideanGaugeProjection (ξ : Covector) (H : Components) : Components :=
  directionProjection ξ * H * directionProjection ξ

/-- The Fourier image of a symmetrized gradient, up to its scalar phase. -/
def gaugeAmplitude (ξ v : Covector) : Components :=
  vecMulVec ξ v + vecMulVec v ξ

/-- The representative in the manuscript's exact gauge decomposition. -/
def euclideanGaugeRepresentative (ξ : Covector) (H : Components) : Covector :=
  (ξ ⬝ᵥ ξ)⁻¹ • (H *ᵥ ξ) - ((ξ ⬝ᵥ (H *ᵥ ξ)) / (2 * (ξ ⬝ᵥ ξ)^2)) • ξ

private theorem dot_sq_ne_zero {ξ : Covector} (hξ : ξ ≠ 0) : ξ ⬝ᵥ ξ ≠ 0 :=
  fun h => hξ (dotProduct_self_eq_zero.mp h)

theorem directionProjection_transpose (ξ : Covector) :
    (directionProjection ξ)ᵀ = directionProjection ξ := by
  simp [directionProjection, transpose_vecMulVec]

theorem directionProjection_kills_covector {ξ : Covector} (hξ : ξ ≠ 0) :
    directionProjection ξ *ᵥ ξ = 0 := by
  rw [directionProjection, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul, inv_mul_cancel₀ (dot_sq_ne_zero hξ), one_smul, sub_self]

theorem directionProjection_idempotent {ξ : Covector} (hξ : ξ ≠ 0) :
    directionProjection ξ * directionProjection ξ = directionProjection ξ := by
  change directionProjection ξ * (1 - (ξ ⬝ᵥ ξ)⁻¹ • vecMulVec ξ ξ) = directionProjection ξ
  rw [mul_sub, mul_one, mul_smul_comm, mul_vecMulVec, directionProjection_kills_covector hξ]
  simp

theorem directionProjection_even (ξ : Covector) :
    directionProjection (-ξ) = directionProjection ξ := by
  have outer : vecMulVec (-ξ) (-ξ) = vecMulVec ξ ξ := by
    ext a b
    simp
  have scalar : (-ξ) ⬝ᵥ (-ξ) = ξ ⬝ᵥ ξ := by
    simp [dotProduct]
  rw [directionProjection, outer, scalar]
  rfl

theorem euclideanGaugeProjection_preserves_symmetry (ξ : Covector) {H : Components}
    (hH : Hᵀ = H) : (euclideanGaugeProjection ξ H)ᵀ = euclideanGaugeProjection ξ H := by
  simp only [euclideanGaugeProjection, transpose_mul, directionProjection_transpose, hH]
  noncomm_ring

theorem euclideanGaugeProjection_idempotent {ξ : Covector} (hξ : ξ ≠ 0) (H : Components) :
    euclideanGaugeProjection ξ (euclideanGaugeProjection ξ H) = euclideanGaugeProjection ξ H := by
  let P := directionProjection ξ
  change P * (P * H * P) * P = P * H * P
  rw [show P * (P * H * P) * P = (P * P) * H * (P * P) by noncomm_ring]
  rw [directionProjection_idempotent hξ]

theorem euclideanGaugeProjection_kills_gauge {ξ : Covector} (hξ : ξ ≠ 0) (v : Covector) :
    euclideanGaugeProjection ξ (gaugeAmplitude ξ v) = 0 := by
  have hr : ξ ᵥ* directionProjection ξ = 0 := by
    rw [← mulVec_transpose, directionProjection_transpose, directionProjection_kills_covector hξ]
  simp only [euclideanGaugeProjection, gaugeAmplitude, mul_add, add_mul, mul_vecMulVec,
    directionProjection_kills_covector hξ, vecMulVec_mul, hr]
  simp

theorem euclideanGaugeProjection_range_kills_covector {ξ : Covector} (hξ : ξ ≠ 0)
    (H : Components) : euclideanGaugeProjection ξ H *ᵥ ξ = 0 := by
  simp only [euclideanGaugeProjection, ← mulVec_mulVec, directionProjection_kills_covector hξ,
    mulVec_zero]

/-- The exact difference between the field and its matrix projection is a
symmetrized-gradient amplitude with the manuscript's chosen coefficient. -/
theorem euclideanGaugeProjection_sub_eq (ξ : Covector) {H : Components} (hH : Hᵀ = H) :
    H - euclideanGaugeProjection ξ H = gaugeAmplitude ξ (euclideanGaugeRepresentative ξ H) := by
  have hv : ξ ᵥ* H = H *ᵥ ξ := by
    rw [← mulVec_transpose, hH]
  simp only [euclideanGaugeProjection, directionProjection, gaugeAmplitude,
    euclideanGaugeRepresentative, sub_mul, mul_sub, one_mul, mul_one, smul_mul_assoc,
    mul_smul_comm, mul_vecMulVec, vecMulVec_mul, vecMulVec_mulVec, op_smul_eq_smul, hv]
  ext a b
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply,
    Pi.sub_apply, Pi.smul_apply, dotProduct_comm (H *ᵥ ξ) ξ, div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  ring

private def componentInner (H K : Components) : ℝ := ∑ a, ∑ b, H a b * K a b

private theorem componentInner_vecMulVec (H : Components) (x y : Covector) :
    componentInner H (vecMulVec x y) = x ⬝ᵥ (H *ᵥ y) := by
  unfold componentInner dotProduct
  apply Finset.sum_congr rfl
  intro a _
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, vecMulVec_apply]
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- Euclidean matrix orthogonality to every pure-gauge amplitude. -/
theorem euclideanGaugeProjection_orthogonal {ξ : Covector} (hξ : ξ ≠ 0)
    {H : Components} (hH : Hᵀ = H) (v : Covector) :
    componentInner (euclideanGaugeProjection ξ H) (gaugeAmplitude ξ v) = 0 := by
  let M := euclideanGaugeProjection ξ H
  have hM : Mᵀ = M := euclideanGaugeProjection_preserves_symmetry ξ hH
  have hx : M *ᵥ ξ = 0 := euclideanGaugeProjection_range_kills_covector hξ H
  have hsum : componentInner M (gaugeAmplitude ξ v) =
      componentInner M (vecMulVec ξ v) + componentInner M (vecMulVec v ξ) := by
    simp [componentInner, gaugeAmplitude, mul_add, Finset.sum_add_distrib]
  rw [hsum, componentInner_vecMulVec, componentInner_vecMulVec, dotProduct_mulVec ξ M v,
    ← mulVec_transpose, hM, hx, dotProduct_zero, zero_dotProduct, add_zero]

end Burnett.P01
