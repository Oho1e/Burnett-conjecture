import Burnett.Analysis.Microlocal.CurlCovariance
import Burnett.Algebra.ComplexPolarization

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.CurlDensity

open Matrix Burnett.RicciSymbol
open scoped BigOperators ComplexOrder

/-- The complexified Christoffel expression on an arbitrary actual first jet. -/
def jetConnection (G : Tensor2) (u : JetSlot → ℂ) (a b c : Index) : ℂ :=
  ∑ d, (G a d : ℂ) * ((u (b, c, d) + u (c, b, d) - u (d, b, c)) / 2)

/-- The principal Ricci system obtained by contracting the connection
divergence, with the Fourier sign used by the metric Ricci symbol. -/
def ricciJetSymbol (G : Tensor2) (ξ : Covector) (u : JetSlot → ℂ) (i : Pair) : ℂ :=
  ∑ a, ((ξ i.2 : ℂ) * jetConnection G u a i.1 a - (ξ a : ℂ) * jetConnection G u a i.1 i.2)

theorem jetConnection_gradient (G : Tensor2) (ξ : Covector) (k : Pair → ℂ) (a b c : Index) :
    jetConnection G (gradientEmbedding ξ *ᵥ k) a b c =
      complexConnectionSymbol G ξ (fun i j => k (i, j)) a b c := by
  simp only [jetConnection, gradientEmbedding_mulVec, complexConnectionSymbol, complexRaiseSecond,
    raiseCovector, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem sum_frequency_raiseSecond (G : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (hG : IsSymmetricTensor G) (hk : IsSymmetricComplexTensor k) (c : Index) :
    (∑ a, (ξ a : ℂ) * complexRaiseSecond G k c a) = complexContracted G ξ k c := by
  simp only [complexRaiseSecond, complexContracted, raiseCovector, Complex.ofReal_sum,
    Complex.ofReal_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  rw [hG d a, hk c a]
  ring

private theorem sum_frequency_raiseCovector (G : Tensor2) (ξ : Covector) :
    (∑ a, (ξ a : ℂ) * (raiseCovector G ξ a : ℂ)) = (symbolNorm G ξ : ℂ) := by
  simp only [raiseCovector, symbolNorm, Complex.ofReal_sum, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  ring

private theorem sum_trace_connection (G : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (hG : IsSymmetricTensor G) (hk : IsSymmetricComplexTensor k) (b : Index) :
    (∑ a, complexConnectionSymbol G ξ k a b a) = (ξ b : ℂ) * complexMetricTrace G k / 2 := by
  have h (a : Index) : (raiseCovector G ξ a : ℂ) * k b a =
      (raiseCovector G ξ a : ℂ) * k a b := by rw [hk b a]
  unfold complexConnectionSymbol
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [sum_frequency_raiseSecond G ξ k hG hk]
  simp only [h]
  change ((ξ b : ℂ) * complexMetricTrace G k + complexContracted G ξ k b -
    complexContracted G ξ k b) / 2 = _
  rw [add_sub_cancel_right]

private theorem sum_divergence_connection (G : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (hG : IsSymmetricTensor G) (hk : IsSymmetricComplexTensor k) (b c : Index) :
    (∑ a, (ξ a : ℂ) * complexConnectionSymbol G ξ k a b c) =
      ((ξ b : ℂ) * complexContracted G ξ k c + (ξ c : ℂ) * complexContracted G ξ k b -
        (symbolNorm G ξ : ℂ) * k b c) / 2 := by
  calc
    (∑ a, (ξ a : ℂ) * complexConnectionSymbol G ξ k a b c) =
        ∑ a, ((ξ b : ℂ) * ((ξ a : ℂ) * complexRaiseSecond G k c a) +
          (ξ c : ℂ) * ((ξ a : ℂ) * complexRaiseSecond G k b a) -
          ((ξ a : ℂ) * (raiseCovector G ξ a : ℂ)) * k b c) / 2 := by
      apply Finset.sum_congr rfl
      intro a _
      unfold complexConnectionSymbol
      ring
    _ = _ := by
      rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.sum_mul,
        sum_frequency_raiseSecond G ξ k hG hk, sum_frequency_raiseSecond G ξ k hG hk,
        sum_frequency_raiseCovector]

/-- On a symmetric rank-one gradient jet, the genuine connection
principal system is the same complex Ricci symbol used in F06. -/
theorem ricciJetSymbol_gradient (G : Tensor2) (ξ : Covector) (k : Pair → ℂ)
    (hG : IsSymmetricTensor G) (hk : IsSymmetricComplexTensor (fun i j => k (i, j))) (i : Pair) :
    ricciJetSymbol G ξ (gradientEmbedding ξ *ᵥ k) i =
      complexRicciSymbol G ξ (fun b c => k (b, c)) i.1 i.2 := by
  unfold ricciJetSymbol
  simp_rw [jetConnection_gradient]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_trace_connection G ξ _ hG hk, sum_divergence_connection G ξ _ hG hk]
  unfold complexRicciSymbol
  ring

def jetConnectionLinear (G : Tensor2) (a b c : Index) : (JetSlot → ℂ) →ₗ[ℂ] ℂ :=
  let eval (i : JetSlot) : (JetSlot → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj i
  ∑ d, ((G a d : ℂ) / 2) •
    (eval (b, c, d) + eval (c, b, d) - eval (d, b, c))

theorem jetConnectionLinear_apply (G : Tensor2) (a b c : Index) (u : JetSlot → ℂ) :
    jetConnectionLinear G a b c u = jetConnection G u a b c := by
  simp only [jetConnectionLinear, jetConnection, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.sub_apply, LinearMap.add_apply, LinearMap.proj_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro d _
  ring

def ricciJetLinear (G : Tensor2) (ξ : Covector) : (JetSlot → ℂ) →ₗ[ℂ] (Pair → ℂ) :=
  LinearMap.pi fun i => ∑ a, ((ξ i.2 : ℂ) • jetConnectionLinear G a i.1 a -
    (ξ a : ℂ) • jetConnectionLinear G a i.1 i.2)

theorem ricciJetLinear_apply (G : Tensor2) (ξ : Covector) (u : JetSlot → ℂ) (i : Pair) :
    ricciJetLinear G ξ u i = ricciJetSymbol G ξ u i := by
  simp only [ricciJetLinear, ricciJetSymbol, LinearMap.pi_apply, LinearMap.sum_apply,
    LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, jetConnectionLinear_apply]

/-- The matrix of the actual finite-dimensional principal system. -/
def ricciJetMatrix (G : Tensor2) (ξ : Covector) : Matrix Pair JetSlot ℂ :=
  LinearMap.toMatrix' (ricciJetLinear G ξ)

theorem ricciJetMatrix_mulVec (G : Tensor2) (ξ : Covector) (u : JetSlot → ℂ) (i : Pair) :
    (ricciJetMatrix G ξ *ᵥ u) i = ricciJetSymbol G ξ u i := by
  rw [ricciJetMatrix, LinearMap.toMatrix'_mulVec, ricciJetLinear_apply]

/-- Curl and Ricci compressions on a single positive jet density put the same
factored amplitude density in the genuine symmetric Ricci symbol kernel. -/
theorem factoredAmplitude_in_complexRicciKernel (G : Tensor2) (ξ η : Covector)
    (hunit : ∑ i, η i * ξ i = 1) (hG : IsSymmetricTensor G)
    (M : Matrix JetSlot JetSlot ℂ) (hM : M.PosSemidef)
    (hMsym : ∀ a b c (j : JetSlot), M (a, b, c) j = M (a, c, b) j)
    (hcurl : curlMatrix ξ * M * (curlMatrix ξ)ᴴ = 0)
    (hRicci : ricciJetMatrix G ξ * M * (ricciJetMatrix G ξ)ᴴ = 0)
    (v : Pair → ℂ) :
    let C := gradientContraction η
    let k (b c : Index) := ((C * M * Cᴴ) *ᵥ v) (b, c)
    IsSymmetricComplexTensor k ∧ ∀ b c, complexRicciSymbol G ξ k b c = 0 := by
  intro C k
  have hcol (b c : Index) (j : JetSlot) : (C * M) (b, c) j = (C * M) (c, b) j := by
    change (C *ᵥ (fun i => M i j)) (b, c) = (C *ᵥ (fun i => M i j)) (c, b)
    change (gradientContraction η *ᵥ (fun i => M i j)) (b, c) =
      (gradientContraction η *ᵥ (fun i => M i j)) (c, b)
    rw [gradientContraction_mulVec, gradientContraction_mulVec]
    simp_rw [hMsym _ b c j]
  have hσ (b c : Index) (j : Pair) : (C * M * Cᴴ) (b, c) j = (C * M * Cᴴ) (c, b) j := by
    change (∑ i, (C * M) (b, c) i * Cᴴ i j) = ∑ i, (C * M) (c, b) i * Cᴴ i j
    simp_rw [hcol b c]
  have hk : IsSymmetricComplexTensor k := by
    intro b c
    change ((C * M * Cᴴ) *ᵥ v) (b, c) = ((C * M * Cᴴ) *ᵥ v) (c, b)
    simp only [Matrix.mulVec, dotProduct]
    simp_rw [hσ b c]
  have hr := factored_range_le_pulled_system_kernel ξ η hunit M hM hcurl (ricciJetMatrix G ξ) hRicci
  have hv : (ricciJetMatrix G ξ * gradientEmbedding ξ) *ᵥ ((C * M * Cᴴ) *ᵥ v) = 0 :=
    hr ⟨v, rfl⟩
  refine ⟨hk, fun b c => ?_⟩
  have hbc := congrFun hv (b, c)
  rw [← Matrix.mulVec_mulVec, ricciJetMatrix_mulVec, ricciJetSymbol_gradient G ξ _ hG hk,
    Pi.zero_apply] at hbc
  exact hbc

end Burnett.Microlocal.CurlDensity
