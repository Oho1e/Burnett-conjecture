import Burnett.Analysis.FrozenScreen.Projection
import Burnett.Algebra.TensorFrame

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol TensorFrame
open scoped Matrix

/-- Orthogonalization of the raised unit direction as in the frozen screen. -/
def screenSecondDirection (B : ScreenMatrix) (e : Covector) : Covector :=
  B *ᵥ e - (e ⬝ᵥ (B *ᵥ e)) • e

/-- The paper's projector Q, given the Euclidean unit covector e. -/
def screenDirectionProjection (B : ScreenMatrix) (e : Covector) : ScreenMatrix :=
  let w := screenSecondDirection B e
  1 - vecMulVec e e - (w ⬝ᵥ w)⁻¹ • vecMulVec w w

theorem screenSecondDirection_dot (B : ScreenMatrix) (e : Covector) (he : e ⬝ᵥ e = 1) :
    e ⬝ᵥ screenSecondDirection B e = 0 := by
  rw [screenSecondDirection, dotProduct_sub, dotProduct_smul, he]
  change e ⬝ᵥ (B *ᵥ e) - (e ⬝ᵥ (B *ᵥ e)) * 1 = 0
  ring

theorem screenSecondDirection_eq_on_null (B : ScreenMatrix) (e : Covector)
    (hs : symbolNorm B e = 0) : screenSecondDirection B e = B *ᵥ e := by
  have h : e ⬝ᵥ (B *ᵥ e) = symbolNorm B e := by
    simp only [symbolNorm, mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [screenSecondDirection, h, hs, zero_smul, sub_zero]

theorem screenSecondDirection_ne_zero_on_null (B : ScreenMatrix) (e : Covector)
    (hB : IsUnit B.det) (he : e ≠ 0) (hs : symbolNorm B e = 0) :
    screenSecondDirection B e ≠ 0 := by
  rw [screenSecondDirection_eq_on_null B e hs]
  intro h
  exact he (mulVec_injective_of_isUnit ((isUnit_iff_isUnit_det B).mpr hB) (h.trans (mulVec_zero B).symm))

theorem screenDirectionProjection_transpose (B : ScreenMatrix) (e : Covector) :
    (screenDirectionProjection B e)ᵀ = screenDirectionProjection B e := by
  simp [screenDirectionProjection, transpose_vecMulVec]

private theorem screenDirectionProjection_mulVec (B : ScreenMatrix) (e v : Covector) :
    screenDirectionProjection B e *ᵥ v =
      v - (e ⬝ᵥ v) • e -
        ((screenSecondDirection B e ⬝ᵥ screenSecondDirection B e)⁻¹ *
          (screenSecondDirection B e ⬝ᵥ v)) • screenSecondDirection B e := by
  simp only [screenDirectionProjection, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec,
    op_smul_eq_smul, smul_smul]

theorem screenDirectionProjection_mulVec_fixed_iff (B : ScreenMatrix) (e v : Covector)
    (he : e ⬝ᵥ e = 1) (hw : screenSecondDirection B e ≠ 0) :
    screenDirectionProjection B e *ᵥ v = v ↔
      e ⬝ᵥ v = 0 ∧ screenSecondDirection B e ⬝ᵥ v = 0 := by
  let w := screenSecondDirection B e
  have hew : e ⬝ᵥ w = 0 := screenSecondDirection_dot B e he
  have hwe : w ⬝ᵥ e = 0 := (dotProduct_comm w e).trans hew
  have hww : w ⬝ᵥ w ≠ 0 := fun hz => hw (dotProduct_self_eq_zero.mp hz)
  have hProjE : e ⬝ᵥ (screenDirectionProjection B e *ᵥ v) = 0 := by
    rw [screenDirectionProjection_mulVec]
    change e ⬝ᵥ (v - (e ⬝ᵥ v) • e - ((w ⬝ᵥ w)⁻¹ * (w ⬝ᵥ v)) • w) = 0
    simp only [dotProduct_sub, dotProduct_smul, he, hew, smul_eq_mul, mul_one, mul_zero, sub_self]
  have hProjW : w ⬝ᵥ (screenDirectionProjection B e *ᵥ v) = 0 := by
    rw [screenDirectionProjection_mulVec]
    change w ⬝ᵥ (v - (e ⬝ᵥ v) • e - ((w ⬝ᵥ w)⁻¹ * (w ⬝ᵥ v)) • w) = 0
    simp only [dotProduct_sub, dotProduct_smul, hwe, smul_eq_mul, mul_zero, sub_zero]
    rw [mul_right_comm, inv_mul_cancel₀ hww, one_mul, sub_self]
  constructor
  · intro h
    rw [h] at hProjE hProjW
    exact ⟨hProjE, hProjW⟩
  · rintro ⟨hE, hW⟩
    simp [screenDirectionProjection_mulVec, hE, hW]

theorem screenDirectionProjection_idempotent (B : ScreenMatrix) (e : Covector)
    (he : e ⬝ᵥ e = 1) (hw : screenSecondDirection B e ≠ 0) :
    screenDirectionProjection B e * screenDirectionProjection B e =
      screenDirectionProjection B e := by
  let w := screenSecondDirection B e
  let Q := screenDirectionProjection B e
  have hew : e ⬝ᵥ w = 0 := screenSecondDirection_dot B e he
  have hww : w ⬝ᵥ w ≠ 0 := fun hz => hw (dotProduct_self_eq_zero.mp hz)
  have hQe : Q *ᵥ e = 0 := by
    rw [screenDirectionProjection_mulVec]
    change e - (e ⬝ᵥ e) • e - ((w ⬝ᵥ w)⁻¹ * (w ⬝ᵥ e)) • w = 0
    rw [he, dotProduct_comm w e, hew]
    simp
  have hQw : Q *ᵥ w = 0 := by
    rw [screenDirectionProjection_mulVec]
    change w - (e ⬝ᵥ w) • e - ((w ⬝ᵥ w)⁻¹ * (w ⬝ᵥ w)) • w = 0
    rw [hew, inv_mul_cancel₀ hww]
    simp
  change Q * (1 - vecMulVec e e - (w ⬝ᵥ w)⁻¹ • vecMulVec w w) = Q
  simp [mul_sub, mul_vecMulVec, hQe, hQw]

theorem screenDirectionProjection_trace (B : ScreenMatrix) (e : Covector)
    (he : e ⬝ᵥ e = 1) (hw : screenSecondDirection B e ≠ 0) :
    Matrix.trace (screenDirectionProjection B e) = 2 := by
  let w := screenSecondDirection B e
  have hww : w ⬝ᵥ w ≠ 0 := fun hz => hw (dotProduct_self_eq_zero.mp hz)
  change Matrix.trace (1 - vecMulVec e e - (w ⬝ᵥ w)⁻¹ • vecMulVec w w) = 2
  simp only [Matrix.trace_sub, Matrix.trace_one, Matrix.trace_smul, Matrix.trace_vecMulVec,
    he, smul_eq_mul, inv_mul_cancel₀ hww]
  norm_num [Fintype.card_fin]

end Burnett.V06
