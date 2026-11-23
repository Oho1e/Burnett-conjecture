import Burnett.Analysis.Microlocal.CompactChartInput
import Burnett.Analysis.Microlocal.PositiveKernel
import Burnett.Algebra.RicciSymbol

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CurlDensity

open Matrix Burnett.RicciSymbol Burnett.Microlocal.PositiveKernel
open scoped BigOperators ComplexOrder

abbrev CurlSlot := Index × Index × Pair

/-- The actual first-order exterior derivative symbol in the derivative index. -/
def curlMatrix (ξ : Covector) : Matrix CurlSlot JetSlot ℂ :=
  fun i j =>
    (if j = (i.2.1, i.2.2) then (ξ i.1 : ℂ) else 0) -
    (if j = (i.1, i.2.2) then (ξ i.2.1 : ℂ) else 0)

/-- The rank-one jet embedding `k ↦ ξ ⊗ k` in ordered coordinates. -/
def gradientEmbedding (ξ : Covector) : Matrix JetSlot Pair ℂ :=
  fun i j => if j = i.2 then (ξ i.1 : ℂ) else 0

/-- Contract the derivative index with a dual vector. -/
def gradientContraction (η : Covector) : Matrix Pair JetSlot ℂ :=
  fun i j => if j.2 = i then (η j.1 : ℂ) else 0

theorem curlMatrix_mulVec (ξ : Covector) (u : JetSlot → ℂ) (i : CurlSlot) :
    (curlMatrix ξ *ᵥ u) i =
      (ξ i.1 : ℂ) * u (i.2.1, i.2.2) - (ξ i.2.1 : ℂ) * u (i.1, i.2.2) := by
  classical
  simp only [Matrix.mulVec, dotProduct, curlMatrix, sub_mul, Finset.sum_sub_distrib, ite_mul,
    zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem gradientEmbedding_mulVec (ξ : Covector) (u : Pair → ℂ) (i : JetSlot) :
    (gradientEmbedding ξ *ᵥ u) i = (ξ i.1 : ℂ) * u i.2 := by
  classical
  simp only [Matrix.mulVec, dotProduct, gradientEmbedding, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]

theorem gradientContraction_mulVec (η : Covector) (u : JetSlot → ℂ) (i : Pair) :
    (gradientContraction η *ᵥ u) i = ∑ j, (η j : ℂ) * u (j, i) := by
  classical
  simp only [Matrix.mulVec, dotProduct, gradientContraction, Fintype.sum_prod_type
    (α₁ := Index) (α₂ := Pair), ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- If `η·ξ = 1`, the projected amplitude reconstructs any curl-free jet. -/
theorem gradient_reconstruct_of_curl_zero (ξ η : Covector) (u : JetSlot → ℂ)
    (hunit : ∑ i, η i * ξ i = 1) (hcurl : curlMatrix ξ *ᵥ u = 0) :
    gradientEmbedding ξ *ᵥ (gradientContraction η *ᵥ u) = u := by
  funext i
  rw [gradientEmbedding_mulVec, gradientContraction_mulVec, Finset.mul_sum]
  have h (j : Index) : (ξ i.1 : ℂ) * u (j, i.2) = (ξ j : ℂ) * u i := by
    have hc := congrFun hcurl (i.1, j, i.2)
    rw [curlMatrix_mulVec, Pi.zero_apply] at hc
    exact sub_eq_zero.mp hc
  have hunit' : ∑ j, (η j : ℂ) * (ξ j : ℂ) = 1 := by exact_mod_cast hunit
  calc
    (∑ j, (ξ i.1 : ℂ) * ((η j : ℂ) * u (j, i.2))) =
        ∑ j, ((η j : ℂ) * (ξ j : ℂ)) * u i := by
      apply Finset.sum_congr rfl
      intro j _
      calc
        (ξ i.1 : ℂ) * ((η j : ℂ) * u (j, i.2)) =
            (η j : ℂ) * ((ξ i.1 : ℂ) * u (j, i.2)) := mul_left_comm _ _ _
        _ = _ := by rw [h j, mul_assoc]
    _ = u i := by rw [← Finset.sum_mul, hunit', one_mul]

/-- The contraction is a left inverse of the rank-one embedding. -/
theorem gradient_leftInverse (ξ η : Covector) (hunit : ∑ i, η i * ξ i = 1) :
    gradientContraction η * gradientEmbedding ξ = 1 := by
  have hunit' : ∑ j, (η j : ℂ) * (ξ j : ℂ) = 1 := by exact_mod_cast hunit
  ext i k
  change (gradientContraction η *ᵥ (fun j => gradientEmbedding ξ j k)) i = _
  rw [gradientContraction_mulVec]
  by_cases hi : k = i
  · subst k
    simpa [gradientEmbedding] using hunit'
  · have hne : i ≠ k := fun h => hi h.symm
    simp [gradientEmbedding, hi, hne]

/-- Factoring a positive jet covariance through the actual curl kernel gives a
positive amplitude covariance in the same ordered coordinates. -/
theorem positive_factorCovariance_of_curl_compression (ξ η : Covector)
    (hunit : ∑ i, η i * ξ i = 1)
    (M : Matrix JetSlot JetSlot ℂ) (hM : M.PosSemidef)
    (hcurl : curlMatrix ξ * M * (curlMatrix ξ)ᴴ = 0) :
    let J := gradientEmbedding ξ
    let C := gradientContraction η
    let σ := C * M * Cᴴ
    σ.PosSemidef ∧ M = J * σ * Jᴴ := by
  intro J C σ
  have hkernel := mul_eq_zero_of_compression_eq_zero hM (curlMatrix ξ) hcurl
  have hL : J * (C * M) = M := by
    ext i j
    let v (k : JetSlot) := M k j
    have hK : curlMatrix ξ *ᵥ v = 0 := by
      funext k
      exact congrArg (fun A : Matrix CurlSlot JetSlot ℂ => A k j) hkernel
    have h := congrFun (gradient_reconstruct_of_curl_zero ξ η v hunit hK) i
    rw [Matrix.mulVec_mulVec] at h
    rw [← Matrix.mul_assoc]
    exact h
  have hR : M * Cᴴ * Jᴴ = M := by
    have h := congrArg Matrix.conjTranspose hL
    simpa only [Matrix.conjTranspose_mul, hM.isHermitian.eq] using h
  refine ⟨hM.mul_mul_conjTranspose_same C, ?_⟩
  change M = (J * ((C * M) * Cᴴ)) * Jᴴ
  rw [← Matrix.mul_assoc, hL, hR]

/-- Any second system compression on the same covariance descends to the
amplitude covariance, using the same embedding and the same witness. -/
theorem factored_range_le_pulled_system_kernel {rows : Type*} (ξ η : Covector)
    (hunit : ∑ i, η i * ξ i = 1)
    (M : Matrix JetSlot JetSlot ℂ) (hM : M.PosSemidef)
    (hcurl : curlMatrix ξ * M * (curlMatrix ξ)ᴴ = 0)
    (A : Matrix rows JetSlot ℂ) (hA : A * M * Aᴴ = 0) :
    let C := gradientContraction η
    LinearMap.range (C * M * Cᴴ).mulVecLin ≤
      LinearMap.ker (A * gradientEmbedding ξ).mulVecLin := by
  intro C
  obtain ⟨hp, hf⟩ := positive_factorCovariance_of_curl_compression ξ η hunit M hM hcurl
  let J := gradientEmbedding ξ
  have hF : M = J * (C * M * Cᴴ) * Jᴴ := hf
  apply range_le_ker_of_compression_eq_zero hp
  calc
    (A * J) * (C * M * Cᴴ) * (A * J)ᴴ = A * (J * (C * M * Cᴴ) * Jᴴ) * Aᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = A * M * Aᴴ := congrArg (fun S : Matrix JetSlot JetSlot ℂ => A * S * Aᴴ) hF.symm
    _ = 0 := hA

/-- The actual inverse auxiliary metric provides the normalized dual on its
unit cosphere. The Lorentzian norm plays no role in this factorization. -/
theorem raised_auxiliary_pairing_of_unit (rInv : Tensor2) (ξ : Covector)
    (hξ : symbolNorm rInv ξ = 1) :
    ∑ i, raiseCovector rInv ξ i * ξ i = 1 := by
  rw [← hξ]
  simp only [raiseCovector, symbolNorm, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Matrix factorization gives exactly the ordered covariance components in
the chart formula, with both real frequency factors. -/
theorem gradient_factor_entry (ξ : Covector) (S : Matrix Pair Pair ℂ) (i j : JetSlot) :
    (gradientEmbedding ξ * S * (gradientEmbedding ξ)ᴴ) i j =
      (ξ i.1 : ℂ) * (ξ j.1 : ℂ) * S i.2 j.2 := by
  classical
  have hE (k : Pair) : (gradientEmbedding ξ * S) i k = (ξ i.1 : ℂ) * S i.2 k :=
    gradientEmbedding_mulVec ξ (fun a => S a k) i
  rw [Matrix.mul_apply]
  simp_rw [hE, Matrix.conjTranspose_apply, gradientEmbedding]
  have h (k : Pair) :
      star (if k = j.2 then (ξ j.1 : ℂ) else 0) =
        if k = j.2 then (ξ j.1 : ℂ) else 0 := by
    by_cases hk : k = j.2 <;> simp [hk]
  simp only [h, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

end Burnett.Microlocal.CurlDensity
