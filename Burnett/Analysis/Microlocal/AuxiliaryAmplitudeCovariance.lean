import Burnett.Analysis.Microlocal.RicciJetSymbol

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.CurlDensity

open Matrix Burnett.RicciSymbol
open scoped BigOperators ComplexOrder

/-- The amplitude covariance in ordered coordinates. The contraction is
with the covector raised by the inverse auxiliary metric. -/
def auxiliaryAmplitudeCovariance (rInv : Tensor2) (ξ : Covector)
    (M : Matrix JetSlot JetSlot ℂ) : Matrix Pair Pair ℂ :=
  let C := gradientContraction (raiseCovector rInv ξ)
  C * M * Cᴴ

theorem amplitudeCovariance_unique (ξ η : Covector) (hunit : ∑ i, η i * ξ i = 1)
    (S : Matrix Pair Pair ℂ) :
    let J := gradientEmbedding ξ
    let C := gradientContraction η
    C * (J * S * Jᴴ) * Cᴴ = S := by
  intro J C
  have h := gradient_leftInverse ξ η hunit
  change C * J = 1 at h
  calc
    C * (J * S * Jᴴ) * Cᴴ = (C * J) * S * (C * J)ᴴ := by
      rw [Matrix.conjTranspose_mul]
      simp only [Matrix.mul_assoc]
    _ = S := by rw [h, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]

/-- The chart amplitude covariance is uniquely determined by the common jet
covariance. Its ordered entries and actual Ricci kernel are given together. -/
theorem auxiliary_covariance_factorization_and_kernel (rInv G : Tensor2) (ξ : Covector)
    (hξ : symbolNorm rInv ξ = 1) (hG : IsSymmetricTensor G)
    (M : Matrix JetSlot JetSlot ℂ) (hM : M.PosSemidef)
    (hMsym : ∀ a b c (j : JetSlot), M (a, b, c) j = M (a, c, b) j)
    (hcurl : curlMatrix ξ * M * (curlMatrix ξ)ᴴ = 0)
    (hRicci : ricciJetMatrix G ξ * M * (ricciJetMatrix G ξ)ᴴ = 0) :
    let J := gradientEmbedding ξ
    let S := auxiliaryAmplitudeCovariance rInv ξ M
    S.PosSemidef ∧
      M = J * S * Jᴴ ∧
      (∀ i j, M i j = (ξ i.1 : ℂ) * (ξ j.1 : ℂ) * S i.2 j.2) ∧
      ∀ v : Pair → ℂ, let k (b c : Index) := (S *ᵥ v) (b, c)
        IsSymmetricComplexTensor k ∧ ∀ b c, complexRicciSymbol G ξ k b c = 0 := by
  intro J S
  let η := raiseCovector rInv ξ
  have hu := raised_auxiliary_pairing_of_unit rInv ξ hξ
  obtain ⟨hp, hF⟩ := positive_factorCovariance_of_curl_compression ξ η hu M hM hcurl
  change M = J * S * Jᴴ at hF
  refine ⟨hp, hF, ?_, ?_⟩
  · intro i j
    exact (congrArg (fun A : Matrix JetSlot JetSlot ℂ => A i j) hF).trans
      (gradient_factor_entry ξ S i j)
  · exact fun v => factoredAmplitude_in_complexRicciKernel G ξ η hu hG M hM hMsym hcurl hRicci v

/-- Constructing the amplitude covariance from measurable coordinate entries
preserves measurability. -/
theorem measurable_auxiliaryAmplitudeCovariance_entry {X : Type*} [MeasurableSpace X]
    (rInv : X → Tensor2) (ξ : X → Covector) (M : X → Matrix JetSlot JetSlot ℂ)
    (hr : ∀ a d, Measurable (fun x => rInv x a d))
    (hξ : ∀ a, Measurable (fun x => ξ x a))
    (hM : ∀ i j, Measurable (fun x => M x i j))
    (i j : Pair) : Measurable (fun x => auxiliaryAmplitudeCovariance (rInv x) (ξ x) (M x) i j) := by
  let C (x : X) := gradientContraction (raiseCovector (rInv x) (ξ x))
  have hc (i : Pair) (j : JetSlot) : Measurable (fun x => C x i j) := by
    have h (a : Index) : Measurable (fun x => raiseCovector (rInv x) (ξ x) a) :=
      Finset.measurable_sum _ fun d _ => (hr a d).mul (hξ d)
    by_cases he : j.2 = i
    · simpa only [C, gradientContraction, if_pos he] using
        Complex.continuous_ofReal.measurable.comp (h j.1)
    · simp only [C, gradientContraction, if_neg he, measurable_const]
  change Measurable (fun x => (C x * M x * (C x)ᴴ) i j)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.measurable_sum _ fun k _ =>
    (Finset.measurable_sum _ fun l _ => (hc i l).mul (hM l k)).mul
      (Complex.continuous_conj.measurable.comp (hc j k))

end Burnett.Microlocal.CurlDensity
