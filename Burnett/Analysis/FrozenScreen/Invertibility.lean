import Burnett.Analysis.FrozenScreen.Directions
import Burnett.Analysis.FrozenScreen.NullOrthogonality

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol TensorFrame
open scoped Matrix

/-- The actual extended screen matrix in the paper is invertible on the null
cone. The proof uses positivity only on the two-dimensional screen. -/
theorem screenMetricExtension_isUnit_on_null
    (B : ScreenMatrix) (frame : LorentzFrame B) (hB : IsUnit B.det)
    (e : Covector) (he : e ⬝ᵥ e = 1) (hn : symbolNorm B e = 0) :
    IsUnit (screenMetricExtension B (screenDirectionProjection B e)).det := by
  let Q := screenDirectionProjection B e
  let A := screenMetricExtension B Q
  have he₀ : e ≠ 0 := by
    intro h
    rw [h, zero_dotProduct] at he
    norm_num at he
  have hw := screenSecondDirection_ne_zero_on_null B e hB he₀ hn
  have hQ : Q * Q = Q := screenDirectionProjection_idempotent B e he hw
  have hQt : Qᵀ = Q := screenDirectionProjection_transpose B e
  have hRest (v : Covector) : Q *ᵥ (Q *ᵥ v) = Q *ᵥ v := by rw [mulVec_mulVec, hQ]
  have hFormula (v : Covector) :
      A *ᵥ v = Q *ᵥ (B *ᵥ (Q *ᵥ v)) + (v - Q *ᵥ v) := by
    simp only [A, screenMetricExtension, add_mulVec, sub_mulVec, one_mulVec, mulVec_mulVec]
    rw [mul_assoc]
  change IsUnit A.det
  rw [← isUnit_iff_isUnit_det, ← mulVec_injective_iff_isUnit]
  intro x y hxy
  let v : Covector := x - y
  have hAv : A *ᵥ v = 0 := by
    rw [show v = x - y from rfl, mulVec_sub, hxy, sub_self]
  have hComplement : Q *ᵥ (v - Q *ᵥ v) = 0 := by rw [mulVec_sub, hRest, sub_self]
  have hQAv : Q *ᵥ (B *ᵥ (Q *ᵥ v)) = 0 := by
    have h : Q *ᵥ (A *ᵥ v) = Q *ᵥ (0 : Covector) := congrArg (Q *ᵥ ·) hAv
    rw [hFormula, mulVec_add, hRest, hComplement, add_zero, mulVec_zero] at h
    exact h
  have hDot : (Q *ᵥ v) ⬝ᵥ (B *ᵥ (Q *ᵥ v)) = 0 := by
    have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ (B *ᵥ (Q *ᵥ v))) = (Q *ᵥ v) ⬝ᵥ (0 : Covector) :=
      congrArg ((Q *ᵥ v) ⬝ᵥ ·) hQAv
    rwa [dotProduct_mulVec (Q *ᵥ v) Q, ← mulVec_transpose, hQt, hRest, dotProduct_zero] at h
  have hQv : Q *ᵥ v = 0 := by
    by_contra hne
    obtain ⟨hE, hW⟩ := (screenDirectionProjection_mulVec_fixed_iff B e _ he hw).mp (hRest v)
    rw [screenSecondDirection_eq_on_null B e hn] at hW
    have hp := screen_quadratic_pos B frame e (Q *ᵥ v) he₀ hn
      ((dotProduct_comm _ _).trans hW) ((dotProduct_comm _ _).trans hE) hne
    exact hp.ne' hDot
  apply sub_eq_zero.mp
  change v = 0
  simpa only [hFormula, hQv, mulVec_zero, sub_zero, zero_add] using hAv

/-- On the null cone the paper's trace-adjusted formula uses an invertible
extended metric and is an idempotent projection. -/
theorem frozenNullScreenProjection_idempotent
    (B : ScreenMatrix) (frame : LorentzFrame B) (hB : IsUnit B.det)
    (e : Covector) (he : e ⬝ᵥ e = 1) (hn : symbolNorm B e = 0) (H : ScreenMatrix) :
    let Q := screenDirectionProjection B e
    frozenScreenProjection B Q (frozenScreenProjection B Q H) = frozenScreenProjection B Q H := by
  intro Q
  have he₀ : e ≠ 0 := by
    intro h
    rw [h, zero_dotProduct] at he
    norm_num at he
  have hw := screenSecondDirection_ne_zero_on_null B e hB he₀ hn
  exact frozenScreenProjection_idempotent B Q H
    (screenDirectionProjection_idempotent B e he hw) (screenDirectionProjection_trace B e he hw)
    (screenMetricExtension_isUnit_on_null B frame hB e he hn)

end Burnett.V06
