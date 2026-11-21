import Burnett.Analysis.FrozenScreen.Projection
import Burnett.Analysis.FrozenScreen.Directions
import Mathlib.Data.Real.Sqrt

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol
open scoped Matrix BigOperators

/-- The Euclidean unit direction used in the frozen screen construction. -/
def screenUnitCovector (ξ : Covector) : Covector := (Real.sqrt (ξ ⬝ᵥ ξ))⁻¹ • ξ

private theorem dot_sq_nonneg (ξ : Covector) : 0 ≤ ξ ⬝ᵥ ξ :=
  Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

private theorem dot_sq_pos (ξ : Covector) (hξ : ξ ≠ 0) : 0 < ξ ⬝ᵥ ξ :=
  lt_of_le_of_ne (dot_sq_nonneg ξ) (fun h => hξ (dotProduct_self_eq_zero.mp h.symm))

theorem screenUnitCovector_unit (ξ : Covector) (hξ : ξ ≠ 0) :
    screenUnitCovector ξ ⬝ᵥ screenUnitCovector ξ = 1 := by
  have hn : Real.sqrt (ξ ⬝ᵥ ξ) ≠ 0 := (Real.sqrt_pos.2 (dot_sq_pos ξ hξ)).ne'
  rw [screenUnitCovector, smul_dotProduct, dotProduct_smul]
  change (Real.sqrt (ξ ⬝ᵥ ξ))⁻¹ * ((Real.sqrt (ξ ⬝ᵥ ξ))⁻¹ * (ξ ⬝ᵥ ξ)) = 1
  calc
    _ = (Real.sqrt (ξ ⬝ᵥ ξ))⁻¹ * ((Real.sqrt (ξ ⬝ᵥ ξ))⁻¹ * (Real.sqrt (ξ ⬝ᵥ ξ))^2) := by
      rw [Real.sq_sqrt (dot_sq_nonneg ξ)]
    _ = 1 := by field_simp

theorem screenUnitCovector_scale (ξ : Covector) (r : ℝ) (hr : 0 < r) :
    screenUnitCovector (r • ξ) = screenUnitCovector ξ := by
  have hquad : (r • ξ) ⬝ᵥ (r • ξ) = r^2 * (ξ ⬝ᵥ ξ) := by
    rw [smul_dotProduct, dotProduct_smul]
    simp only [smul_eq_mul]
    ring
  rw [screenUnitCovector, screenUnitCovector, hquad, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq hr.le, smul_smul, _root_.mul_inv_rev, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

theorem screenUnitCovector_neg (ξ : Covector) :
    screenUnitCovector (-ξ) = -screenUnitCovector ξ := by
  simp [screenUnitCovector, neg_dotProduct, dotProduct_neg]

theorem screenSecondDirection_neg (B : ScreenMatrix) (e : Covector) :
    screenSecondDirection B (-e) = -screenSecondDirection B e := by
  simp only [screenSecondDirection, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, smul_neg]
  abel

theorem screenDirectionProjection_neg (B : ScreenMatrix) (e : Covector) :
    screenDirectionProjection B (-e) = screenDirectionProjection B e := by
  simp [screenDirectionProjection, screenSecondDirection_neg, neg_vecMulVec, vecMulVec_neg,
    neg_dotProduct, dotProduct_neg]

/-- Substitution of the paper's Euclidean unit direction into the exact
trace-adjusted matrix formula. -/
def frozenScreenSymbol (B H : ScreenMatrix) (ξ : Covector) : ScreenMatrix :=
  frozenScreenProjection B (screenDirectionProjection B (screenUnitCovector ξ)) H

theorem frozenScreenSymbol_even (B H : ScreenMatrix) (ξ : Covector) :
    frozenScreenSymbol B H (-ξ) = frozenScreenSymbol B H ξ := by
  simp only [frozenScreenSymbol, screenUnitCovector_neg, screenDirectionProjection_neg]

theorem frozenScreenSymbol_degreeZero (B H : ScreenMatrix) (ξ : Covector) (r : ℝ) (hr : 0 < r) :
    frozenScreenSymbol B H (r • ξ) = frozenScreenSymbol B H ξ := by
  simp only [frozenScreenSymbol, screenUnitCovector_scale ξ r hr]

end Burnett.V06
