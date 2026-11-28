import Burnett.Analysis.TransportPatches.ScreenGlobalCutoffSupport
import Burnett.Analysis.FrozenScreen.Directions
import Burnett.Analysis.FrozenScreen.Symbol

set_option autoImplicit false
set_option maxRecDepth 5500
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol
open scoped Matrix

open private screenDirectionProjection_mulVec from Burnett.Analysis.FrozenScreen.Directions
open private dot_sq_pos from Burnett.Analysis.FrozenScreen.Symbol

private theorem wardScreenDirection_kills_metricDirection (B : ScreenMatrix) (e : Covector)
    (he : e ⬝ᵥ e = 1) : screenDirectionProjection B e *ᵥ (B *ᵥ e) = 0 := by
  let w := screenSecondDirection B e
  let Q := screenDirectionProjection B e
  have hew : e ⬝ᵥ w = 0 := screenSecondDirection_dot B e he
  have hwe : w ⬝ᵥ e = 0 := (dotProduct_comm w e).trans hew
  have hQe : Q *ᵥ e = 0 := by
    dsimp only [Q]
    rw [screenDirectionProjection_mulVec]
    change e - (e ⬝ᵥ e) • e - ((w ⬝ᵥ w)⁻¹ * (w ⬝ᵥ e)) • w = 0
    rw [he, hwe]
    simp
  have hQw : Q *ᵥ w = 0 := by
    by_cases hw : w = 0
    · simp [hw]
    · dsimp only [Q]
      rw [screenDirectionProjection_mulVec]
      change w - (e ⬝ᵥ w) • e - ((w ⬝ᵥ w)⁻¹ * (w ⬝ᵥ w)) • w = 0
      have hww : w ⬝ᵥ w ≠ 0 := fun h => hw (dotProduct_self_eq_zero.mp h)
      rw [hew, inv_mul_cancel₀ hww]
      simp
  have hBe : B *ᵥ e = w + (e ⬝ᵥ (B *ᵥ e)) • e := by
    change B *ᵥ e = (B *ᵥ e - (e ⬝ᵥ (B *ᵥ e)) • e) + (e ⬝ᵥ (B *ᵥ e)) • e
    rw [sub_add_cancel]
  change Q *ᵥ (B *ᵥ e) = 0
  rw [hBe, mulVec_add, mulVec_smul, hQw, hQe]
  simp

private theorem wardScreenDirection_kills_metricCovector (B : ScreenMatrix) (q : Covector) :
    screenDirectionProjection B (screenUnitCovector q) *ᵥ (B *ᵥ q) = 0 := by
  by_cases hq : q = 0
  · simp [hq]
  let e := screenUnitCovector q
  let s := Real.sqrt (q ⬝ᵥ q)
  have hs : s ≠ 0 := (Real.sqrt_pos.2 (dot_sq_pos q hq)).ne'
  have he := screenUnitCovector_unit q hq
  have hq' : s • e = q := smul_inv_smul₀ hs q
  change screenDirectionProjection B e *ᵥ (B *ᵥ q) = 0
  have hb : B *ᵥ q = s • (B *ᵥ e) := by
    rw [← mulVec_smul, hq']
  rw [hb, mulVec_smul, wardScreenDirection_kills_metricDirection B e he, smul_zero]

/-- The actual wide-screen column and its transpose kill the metric-raised
covector pointwise, independently of whether the input column is symmetric.
The angular cutoff and the inverse in the trace correction are retained. -/
theorem globalAngularScreenSymbol_kills_metricCovector (r R : ℝ) (B H : ScreenMatrix) (q : Covector) :
    globalAngularScreenSymbol r R B H q *ᵥ (B *ᵥ q) = 0 ∧
      (globalAngularScreenSymbol r R B H q)ᵀ *ᵥ (B *ᵥ q) = 0 := by
  let Q := screenDirectionProjection B (screenUnitCovector q)
  have hQ : Q *ᵥ (B *ᵥ q) = 0 := wardScreenDirection_kills_metricCovector B q
  have hQt : Qᵀ = Q := screenDirectionProjection_transpose B (screenUnitCovector q)
  let c := angularScreenCutoff r R (symbolNorm B (screenUnitCovector q))
  change (c • frozenScreenProjection B Q H) *ᵥ (B *ᵥ q) = 0 ∧
    (c • frozenScreenProjection B Q H)ᵀ *ᵥ (B *ᵥ q) = 0
  constructor
  · simp only [frozenScreenProjection, screenInverse, smul_mulVec, sub_mulVec, ← mulVec_mulVec, hQ, mulVec_zero,
      smul_zero, sub_zero]
  · simp only [frozenScreenProjection, screenInverse, transpose_smul, transpose_sub, transpose_mul, hQt,
      smul_mulVec, sub_mulVec, ← mulVec_mulVec, hQ, mulVec_zero, smul_zero, sub_zero]

end Burnett.V06
