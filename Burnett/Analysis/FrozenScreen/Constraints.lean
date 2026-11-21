import Burnett.Analysis.FrozenScreen.Invertibility

set_option autoImplicit false
set_option maxHeartbeats 2300000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol TensorFrame
open scoped Matrix

private theorem screenDirectionProjection_left_fixed_iff
    (B H : ScreenMatrix) (e : Covector) (he : e ⬝ᵥ e = 1)
    (hw : screenSecondDirection B e ≠ 0) :
    screenDirectionProjection B e * H = H ↔
      Hᵀ *ᵥ e = 0 ∧ Hᵀ *ᵥ screenSecondDirection B e = 0 := by
  let Q := screenDirectionProjection B e
  let w := screenSecondDirection B e
  let col (j : Index) : Covector := fun i => H i j
  have hCol (j : Index) : (Q *ᵥ col j) = fun i => (Q * H) i j := rfl
  constructor
  · intro Hfix
    have hOrth (j : Index) : e ⬝ᵥ col j = 0 ∧ w ⬝ᵥ col j = 0 := by
      apply (screenDirectionProjection_mulVec_fixed_iff B e (col j) he hw).mp
      rw [hCol, Hfix]
    constructor
    · funext j
      change col j ⬝ᵥ e = 0
      exact (dotProduct_comm _ _).trans (hOrth j).1
    · funext j
      change col j ⬝ᵥ w = 0
      exact (dotProduct_comm _ _).trans (hOrth j).2
  · rintro ⟨hE, hW⟩
    ext i j
    have hOrth : e ⬝ᵥ col j = 0 ∧ w ⬝ᵥ col j = 0 := by
      exact ⟨(dotProduct_comm _ _).trans (congrFun hE j),
        (dotProduct_comm _ _).trans (congrFun hW j)⟩
    have h := congrFun ((screenDirectionProjection_mulVec_fixed_iff B e (col j) he hw).mpr hOrth) i
    exact h

private theorem screenDirectionConstraints_iff (B H : ScreenMatrix) (e : Covector) :
    H *ᵥ e = 0 ∧ H *ᵥ screenSecondDirection B e = 0 ↔
      H *ᵥ e = 0 ∧ H *ᵥ (B *ᵥ e) = 0 := by
  have hW : H *ᵥ screenSecondDirection B e =
      H *ᵥ (B *ᵥ e) - (e ⬝ᵥ (B *ᵥ e)) • (H *ᵥ e) := by
    rw [screenSecondDirection, mulVec_sub, mulVec_smul]
  constructor <;> rintro ⟨hE, h⟩
  · exact ⟨hE, by simpa only [hW, hE, smul_zero, sub_zero] using h⟩
  · exact ⟨hE, by simp only [hW, hE, h, smul_zero, sub_zero]⟩

/-- The paper's trace-adjusted projection fixes exactly the symmetric
matrices satisfying both screen contractions and the B-trace constraint. -/
theorem frozenScreenProjection_fixed_iff
    (B H : ScreenMatrix) (hH : Hᵀ = H) (e : Covector) (he : e ⬝ᵥ e = 1)
    (hw : screenSecondDirection B e ≠ 0)
    (hA : IsUnit (screenMetricExtension B (screenDirectionProjection B e)).det) :
    frozenScreenProjection B (screenDirectionProjection B e) H = H ↔
      H *ᵥ e = 0 ∧ H *ᵥ (B *ᵥ e) = 0 ∧ Matrix.trace (B * H) = 0 := by
  let Q := screenDirectionProjection B e
  let P := frozenScreenProjection B Q H
  have hQ : Q * Q = Q := screenDirectionProjection_idempotent B e he hw
  have hQt : Qᵀ = Q := screenDirectionProjection_transpose B e
  have hT : Matrix.trace Q = 2 := screenDirectionProjection_trace B e he hw
  have hLeft : Q * H = H ↔ H *ᵥ e = 0 ∧ H *ᵥ (B *ᵥ e) = 0 := by
    rw [screenDirectionProjection_left_fixed_iff B H e he hw, hH, screenDirectionConstraints_iff]
  change P = H ↔ _
  constructor
  · intro h
    obtain ⟨hL, _, ht⟩ := frozenScreenProjection_range B Q H hQ hT hA
    change Q * P = P at hL
    change Matrix.trace (B * P) = 0 at ht
    rw [h] at hL ht
    exact ⟨(hLeft.mp hL).1, (hLeft.mp hL).2, ht⟩
  · rintro ⟨hE, hB, ht⟩
    have hL : Q * H = H := hLeft.mpr ⟨hE, hB⟩
    have hR : H * Q = H := by
      have hh := congrArg Matrix.transpose hL
      rwa [transpose_mul, hH, hQt] at hh
    change Q * H * Q - (Matrix.trace (B * (Q * H * Q)) / 2) • screenInverse B Q = H
    rw [hL, hR, ht, zero_div, zero_smul, sub_zero]

theorem frozenScreenProjection_symmetric (B H : ScreenMatrix) (e : Covector)
    (hB : Bᵀ = B) (hH : Hᵀ = H) :
    (frozenScreenProjection B (screenDirectionProjection B e) H)ᵀ =
      frozenScreenProjection B (screenDirectionProjection B e) H := by
  let Q := screenDirectionProjection B e
  let A := screenMetricExtension B Q
  have hQ : Qᵀ = Q := screenDirectionProjection_transpose B e
  have hAt : Aᵀ = A := by
    simp only [A, screenMetricExtension, transpose_add, transpose_sub, transpose_one,
      transpose_mul, hQ, hB, mul_assoc]
  have hInv : (screenInverse B Q)ᵀ = screenInverse B Q := by
    change (Q * A⁻¹ * Q)ᵀ = Q * A⁻¹ * Q
    simp only [transpose_mul, hQ, transpose_nonsing_inv, hAt, mul_assoc]
  change (Q * H * Q - (Matrix.trace (B * (Q * H * Q)) / 2) • screenInverse B Q)ᵀ = _
  simp only [frozenScreenProjection, transpose_sub, transpose_smul, hInv, transpose_mul, hQ, hH, mul_assoc]
  rfl

/-- On the null cone the actual screen projection lands in the paper's
three constraints for every symmetric input. -/
theorem frozenNullScreenProjection_constraints
    (B H : ScreenMatrix) (frame : LorentzFrame B) (hB : IsUnit B.det) (hH : Hᵀ = H)
    (e : Covector) (he : e ⬝ᵥ e = 1) (hn : symbolNorm B e = 0) :
    let P := frozenScreenProjection B (screenDirectionProjection B e) H
    P *ᵥ e = 0 ∧ P *ᵥ (B *ᵥ e) = 0 ∧ Matrix.trace (B * P) = 0 := by
  intro P
  have he₀ : e ≠ 0 := by
    intro h
    rw [h, zero_dotProduct] at he
    norm_num at he
  have hw := screenSecondDirection_ne_zero_on_null B e hB he₀ hn
  have hBt : Bᵀ = B := by
    ext i j
    exact LorentzPhysical.metric_symmetric B frame j i
  exact (frozenScreenProjection_fixed_iff B P (frozenScreenProjection_symmetric B H e hBt hH)
    e he hw (screenMetricExtension_isUnit_on_null B frame hB e he hn)).mp
    (frozenNullScreenProjection_idempotent B frame hB e he hn H)

end Burnett.V06
