import Burnett.Analysis.GaugeProjection.PrincipalGaugeProjectionAlgebra

set_option autoImplicit false
set_option maxHeartbeats 4100000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.P01
open scoped BigOperators Matrix

private def castDirection (v : Index → ℝ) : Index → ℂ := fun a => (v a : ℂ)

/-- The paper's three coordinate constraints for a symmetric screen tensor. -/
def IsScreenTensor (G : Tensor2) (ξ : E) (H : ComplexTensor2) : Prop :=
  IsSymmetricComplexTensor H ∧
    Matrix.of H *ᵥ castDirection (fun i => ξ i) = 0 ∧
    Matrix.of H *ᵥ castDirection (raiseCovector G (fun i => ξ i)) = 0 ∧
    complexMetricTrace G H = 0

private theorem castDirectionProjection_kills (x : Index → ℝ) (hx : x ≠ 0) :
    (directionProjection x).map Complex.ofReal *ᵥ castDirection x = 0 := by
  funext i
  have h := congrArg Complex.ofReal (congrFun (directionProjection_kills_covector hx) i)
  simpa only [Matrix.mulVec, dotProduct, castDirection, Matrix.map_apply,
    Complex.ofReal_sum, Complex.ofReal_mul, Pi.zero_apply, Complex.ofReal_zero] using h

private theorem principalGaugeProjection_euclidean_transverse (ξ : E) (H : ComplexTensor2)
    (hξ : (fun i : Index => ξ i) ≠ 0) :
    principalGaugeProjection ξ H *ᵥ castDirection (fun i => ξ i) = 0 := by
  unfold principalGaugeProjection
  simp only [← mulVec_mulVec, castDirectionProjection_kills _ hξ, mulVec_zero]

private theorem screen_metricTransverse_iff (G : Tensor2) (ξ : E) (H : ComplexTensor2)
    (hS : IsSymmetricComplexTensor H) :
    Matrix.of H *ᵥ castDirection (raiseCovector G (fun i => ξ i)) = 0 ↔
      ∀ b, complexContracted G (fun i => ξ i) H b = 0 := by
  have h (b : Index) : (Matrix.of H *ᵥ castDirection (raiseCovector G (fun i => ξ i))) b =
      complexContracted G (fun i => ξ i) H b := by
    unfold complexContracted Matrix.mulVec dotProduct
    apply Finset.sum_congr rfl
    intro a _
    change H b a * (raiseCovector G (fun i => ξ i) a : ℂ) = _
    rw [hS b a, mul_comm]
  constructor
  · intro hzero b
    rw [← h, hzero, Pi.zero_apply]
  · intro hzero
    funext b
    rw [h, hzero, Pi.zero_apply]

private theorem castProjection_explicit (x : Index → ℝ) :
    (directionProjection x).map Complex.ofReal =
      (1 : Matrix Index Index ℂ) -
        (((x ⬝ᵥ x)⁻¹ : ℝ) : ℂ) • vecMulVec (castDirection x) (castDirection x) := by
  classical
  ext i j
  simp only [directionProjection, Matrix.map_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, smul_eq_mul, vecMulVec_apply, castDirection, Complex.ofReal_sub, Complex.ofReal_mul]
  split_ifs <;> norm_num

private theorem principalGaugeProjection_fixes_transverse (ξ : E) (H : ComplexTensor2)
    (hS : IsSymmetricComplexTensor H)
    (hE : Matrix.of H *ᵥ castDirection (fun i => ξ i) = 0) :
    principalGaugeProjection ξ H = Matrix.of H := by
  let x := castDirection (fun i : Index => ξ i)
  let Hm := Matrix.of H
  have hT : Hmᵀ = Hm := by ext i j; exact hS j i
  have hL : x ᵥ* Hm = 0 := by rw [← mulVec_transpose, hT]; exact hE
  let c : ℂ := (((fun i : Index => ξ i) ⬝ᵥ (fun i : Index => ξ i))⁻¹ : ℝ)
  unfold principalGaugeProjection
  rw [castProjection_explicit]
  change (1 - c • vecMulVec x x) * Hm * (1 - c • vecMulVec x x) = Hm
  have hleft : (1 - c • vecMulVec x x) * Hm = Hm := by
    rw [sub_mul, one_mul, smul_mul_assoc, vecMulVec_mul, hL, vecMulVec_zero, smul_zero, sub_zero]
  rw [hleft, mul_sub, mul_one, mul_smul_comm, mul_vecMulVec, hE, zero_vecMulVec, smul_zero, sub_zero]

/-- Euclidean transversality and the Lorenz contraction force zero metric
trace on a nonzero null covector, hence also metric transversality. -/
theorem screen_of_projected_nullRicciKernel (G : Tensor2) (ξ : E) (K : ComplexTensor2)
    (hG : IsSymmetricTensor G) (hS : IsSymmetricComplexTensor K)
    (hξ : (fun i : Index => ξ i) ≠ 0) (hs : symbolNorm G (fun i => ξ i) = 0)
    (hR : ∀ a b, complexRicciSymbol G (fun i => ξ i) K a b = 0) :
    IsScreenTensor G ξ (principalGaugeProjection ξ K) := by
  let H : ComplexTensor2 := principalGaugeProjection ξ K
  let x : Index → ℝ := fun i => ξ i
  have hTrans : Matrix.of H *ᵥ castDirection x = 0 :=
    principalGaugeProjection_euclidean_transverse ξ K hξ
  have hSym : IsSymmetricComplexTensor H := by
    obtain ⟨v, hv⟩ := principalGaugeProjection_adds_pureGauge ξ K hS
    change IsSymmetricComplexTensor (principalGaugeProjection ξ K)
    rw [hv]
    intro i j
    change K i j + complexPureGauge x v i j = K j i + complexPureGauge x v j i
    rw [hS i j, complexPureGauge_symmetric _ _ i j]
  have hLor (b : Index) : complexContracted G x H b =
      complexMetricTrace G H * ((x b / 2 : ℝ) : ℂ) :=
    principalGaugeProjection_null_contracted G ξ K hG hS hξ hs hR b
  have hZero : (∑ b, complexContracted G x H b * (x b : ℂ)) = 0 := by
    simp only [complexContracted, Finset.sum_mul]
    rw [Finset.sum_comm]
    simp_rw [mul_assoc, ← Finset.mul_sum]
    apply Finset.sum_eq_zero
    intro a _
    have h0 := congrFun hTrans a
    change (∑ b : Index, H a b * (x b : ℂ)) = 0 at h0
    rw [h0, mul_zero]
  have hNonzero : (∑ b : Index, ((x b / 2 : ℝ) : ℂ) * (x b : ℂ)) ≠ 0 := by
    have hx : (x ⬝ᵥ x) ≠ 0 := fun h => hξ (dotProduct_self_eq_zero.mp h)
    have he : (∑ b : Index, ((x b / 2 : ℝ) : ℂ) * (x b : ℂ)) =
        (((x ⬝ᵥ x) / 2 : ℝ) : ℂ) := by
      rw [dotProduct, Finset.sum_div, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro b _
      push_cast
      ring
    rw [he]
    exact Complex.ofReal_ne_zero.mpr (div_ne_zero hx (by norm_num))
  have hTrace : complexMetricTrace G H = 0 := by
    simp_rw [hLor, mul_assoc, ← Finset.mul_sum] at hZero
    exact (mul_eq_zero.mp hZero).resolve_right hNonzero
  have hContract (b : Index) : complexContracted G x H b = 0 := by rw [hLor, hTrace, zero_mul]
  exact ⟨hSym, hTrans, (screen_metricTransverse_iff G ξ H hSym).2 hContract, hTrace⟩

/-- On a nonzero null covector the original Euclidean gauge complement of
the symmetric Ricci kernel has exactly the paper's screen range. -/
theorem screen_iff_projected_nullRicciKernel (G : Tensor2) (ξ : E) (H : ComplexTensor2)
    (hG : IsSymmetricTensor G) (hξ : (fun i : Index => ξ i) ≠ 0)
    (hs : symbolNorm G (fun i => ξ i) = 0) :
    IsScreenTensor G ξ H ↔ ∃ K : ComplexTensor2,
      IsSymmetricComplexTensor K ∧
      (∀ i j, complexRicciSymbol G (fun a => ξ a) K i j = 0) ∧
      (principalGaugeProjection ξ K : ComplexTensor2) = H := by
  constructor
  · rintro ⟨hS, hE, hM, hTrace⟩
    have hContract := (screen_metricTransverse_iff G ξ H hS).1 hM
    refine ⟨H, hS, ?_, principalGaugeProjection_fixes_transverse ξ H hS hE⟩
    intro a b
    simp [complexRicciSymbol, hs, hTrace, hContract]
  · rintro ⟨K, hSym, hRic, rfl⟩
    exact screen_of_projected_nullRicciKernel G ξ K hG hSym hξ hs hRic

end Burnett.V06
