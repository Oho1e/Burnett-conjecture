import Burnett.Analysis.FrozenScreen.CompactFamily
import Burnett.Analysis.FrozenScreen.Symbol

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol TensorFrame
open scoped Matrix BigOperators

/-- Adding the Euclidean complement makes the restriction to a symmetric
idempotent screen invertible whenever the restricted form is positive. -/
theorem screenMetricExtension_isUnit_of_positive_restriction
    (B Q : ScreenMatrix) (hQt : Qᵀ = Q) (hQ : Q * Q = Q)
    (hPos : ∀ v : Covector, Q *ᵥ v = v → v ≠ 0 → 0 < v ⬝ᵥ (B *ᵥ v)) :
    IsUnit (screenMetricExtension B Q).det := by
  let A := screenMetricExtension B Q
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
    rwa [hFormula, mulVec_add, hRest, hComplement, add_zero, mulVec_zero] at h
  have hDot : (Q *ᵥ v) ⬝ᵥ (B *ᵥ (Q *ᵥ v)) = 0 := by
    have h : (Q *ᵥ v) ⬝ᵥ (Q *ᵥ (B *ᵥ (Q *ᵥ v))) = (Q *ᵥ v) ⬝ᵥ (0 : Covector) :=
      congrArg ((Q *ᵥ v) ⬝ᵥ ·) hQAv
    rwa [dotProduct_mulVec (Q *ᵥ v) Q, ← mulVec_transpose, hQt, hRest, dotProduct_zero] at h
  have hQv : Q *ᵥ v = 0 := by
    by_contra hne
    exact (hPos _ (hRest v) hne).ne' hDot
  apply sub_eq_zero.mp
  change v = 0
  simpa only [hFormula, hQv, mulVec_zero, sub_zero, zero_add] using hAv

/-- The metric of the explicit screen formula is invertible on a single
wide neighborhood for the whole compact family. -/
theorem exists_uniform_wide_screen_invertibility
    (K : Set ScreenMatrix) (hK : IsCompact K)
    (hInv : ∀ B ∈ K, IsUnit B.det) (hFrame : ∀ B ∈ K, Nonempty (LorentzFrame B)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ B ∈ K, ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm B e| < ε →
      screenSecondDirection B e ≠ 0 ∧
      IsUnit (screenMetricExtension B (screenDirectionProjection B e)).det := by
  obtain ⟨ε, δ, c, hε, hδ, hc, hWide⟩ := exists_uniform_wide_screen_bounds K hK hInv hFrame
  refine ⟨ε, hε, ?_⟩
  intro B hB e he hNear
  obtain ⟨hLength, hPos⟩ := hWide B hB e he hNear
  have hw : screenSecondDirection B e ≠ 0 := by
    intro hz
    rw [hz, zero_dotProduct] at hLength
    exact (not_le_of_gt hδ) hLength
  refine ⟨hw, screenMetricExtension_isUnit_of_positive_restriction B (screenDirectionProjection B e)
    (screenDirectionProjection_transpose B e) (screenDirectionProjection_idempotent B e he hw) ?_⟩
  intro v hFix hv
  obtain ⟨heV, hwV⟩ := (screenDirectionProjection_mulVec_fixed_iff B e v he hw).mp hFix
  have hE : v ⬝ᵥ e = 0 := (dotProduct_comm _ _).trans heV
  have hBe : v ⬝ᵥ (B *ᵥ e) = 0 := by
    have hh : v ⬝ᵥ screenSecondDirection B e = 0 := (dotProduct_comm _ _).trans hwV
    rwa [screenSecondDirection, dotProduct_sub, dotProduct_smul, hE, smul_zero, sub_zero] at hh
  let u := screenUnitCovector v
  let a : ℝ := (Real.sqrt (v ⬝ᵥ v))⁻¹
  have ha : 0 < a := by
    apply inv_pos.mpr
    apply Real.sqrt_pos.2
    refine lt_of_le_of_ne (Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)) ?_
    exact fun h => hv (dotProduct_self_eq_zero.mp h.symm)
  have hE' : u ⬝ᵥ e = 0 := by rw [show u = a • v from rfl, smul_dotProduct, hE, smul_zero]
  have hBe' : u ⬝ᵥ (B *ᵥ e) = 0 := by
    rw [show u = a • v from rfl, smul_dotProduct, hBe, smul_zero]
  have hu := hc.trans_le (hPos u (screenUnitCovector_unit v hv) hE' hBe')
  rw [show u = a • v from rfl, mulVec_smul, smul_dotProduct, dotProduct_smul] at hu
  exact (mul_pos_iff_of_pos_left ha).mp ((mul_pos_iff_of_pos_left ha).mp hu)

end Burnett.V06
