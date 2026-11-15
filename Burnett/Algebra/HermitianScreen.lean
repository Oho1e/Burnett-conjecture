import Burnett.Algebra.ComplexPolarization
import Burnett.Algebra.NullScreen

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators ComplexConjugate

private theorem hs_sum_comm (f : Index → Index → ℝ) :
    (∑ a, ∑ b, f a b) = ∑ b, ∑ a, f a b := by
  classical
  have h (s : Finset Index) :
      (∑ a ∈ s, ∑ b, f a b) = ∑ b, ∑ a ∈ s, f a b := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, ih, Finset.sum_add_distrib]
  simpa using h Finset.univ

private theorem hs_dual_pairing (gInv : Tensor2) (ξ v : Covector)
    (hg : IsSymmetricTensor gInv) :
    (∑ a, raiseCovector gInv ξ a * v a) = ∑ a, ξ a * raiseCovector gInv v a := by
  simp only [raiseCovector, Finset.sum_mul, Finset.mul_sum]
  rw [hs_sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [hg b a]
  ring

theorem contracted_pureGauge (gInv : Tensor2) (ξ v : Covector)
    (hg : IsSymmetricTensor gInv) (b : Index) :
    contracted gInv ξ (pureGauge ξ v) b =
      symbolNorm gInv ξ * v b + (∑ a, ξ a * raiseCovector gInv v a) * ξ b := by
  have hn : (∑ a, raiseCovector gInv ξ a * ξ a) = symbolNorm gInv ξ := by
    simp only [raiseCovector, symbolNorm, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro d hd
    ring
  calc
    _ = (∑ a, raiseCovector gInv ξ a * ξ a) * v b +
        (∑ a, raiseCovector gInv ξ a * v a) * ξ b := by
      simp [contracted, pureGauge, mul_add, Finset.sum_add_distrib, Finset.sum_mul, mul_assoc]
    _ = _ := by rw [hn, hs_dual_pairing gInv ξ v hg]

/-- Every actual gauge tensor lies in the Ricci-symbol kernel, for any real
frequency and symmetric inverse metric; nullness is not required. -/
theorem ricciSymbol_pureGauge_eq_zero (gInv : Tensor2) (ξ v : Covector)
    (hg : IsSymmetricTensor gInv) (a b : Index) :
    ricciSymbol gInv ξ (pureGauge ξ v) a b = 0 := by
  simp only [ricciSymbol, contracted_pureGauge gInv ξ v hg,
    metricTrace_pureGauge gInv ξ v hg, pureGauge]
  ring

theorem physicalPairing_add_pureGauge_right
    (gInv : Tensor2) (ξ : Covector) (k l : Tensor2) (v : Covector)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricTensor k)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    physicalPairing gInv k (l + pureGauge ξ v) = physicalPairing gInv k l := by
  rw [physicalPairing_add_right,
    physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ k v hg hkSymm hξ hs hk,
    add_zero]

theorem physicalPairing_add_pureGauge_left
    (gInv : Tensor2) (ξ : Covector) (k l : Tensor2) (v : Covector)
    (hg : IsSymmetricTensor gInv) (hlSymm : IsSymmetricTensor l)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hl : ∀ a b, ricciSymbol gInv ξ l a b = 0) :
    physicalPairing gInv (k + pureGauge ξ v) l = physicalPairing gInv k l := by
  rw [physicalPairing_add_left, physicalPairing_comm gInv (pureGauge ξ v) l hg,
    physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ l v hg hlSymm hξ hs hl,
    add_zero]

theorem physicalPairing_add_pureGauge_both
    (gInv : Tensor2) (ξ : Covector) (k l : Tensor2) (v w : Covector)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricTensor k)
    (hlSymm : IsSymmetricTensor l) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, ricciSymbol gInv ξ l a b = 0) :
    physicalPairing gInv (k + pureGauge ξ v) (l + pureGauge ξ w) = physicalPairing gInv k l := by
  have hlS : IsSymmetricTensor (l + pureGauge ξ w) := by
    intro a b
    change l a b + pureGauge ξ w a b = l b a + pureGauge ξ w b a
    rw [hlSymm a b]
    simp only [pureGauge]
    ring
  have hlK : ∀ a b, ricciSymbol gInv ξ (l + pureGauge ξ w) a b = 0 := by
    intro a b
    rw [ricciSymbol_add, hl a b, ricciSymbol_pureGauge_eq_zero gInv ξ w hg, add_zero]
  rw [physicalPairing_add_pureGauge_left gInv ξ k _ v hg hlS hξ hs hlK,
    physicalPairing_add_pureGauge_right gInv ξ k l w hg hkSymm hξ hs hk]

theorem complexRicciSymbol_pureGauge_eq_zero (gInv : Tensor2) (ξ : Covector)
    (v : ComplexCovector) (hg : IsSymmetricTensor gInv) :
    ∀ a b, complexRicciSymbol gInv ξ (complexPureGauge ξ v) a b = 0 := by
  apply (complexRicci_kernel_iff gInv ξ (complexPureGauge ξ v)).mpr
  constructor
  · simpa only [tensorRe_complexPureGauge] using
      ricciSymbol_pureGauge_eq_zero gInv ξ (fun a => (v a).re) hg
  · simpa only [tensorIm_complexPureGauge] using
      ricciSymbol_pureGauge_eq_zero gInv ξ (fun a => (v a).im) hg

theorem complexPureGauge_symmetric (ξ : Covector) (v : ComplexCovector) :
    IsSymmetricComplexTensor (complexPureGauge ξ v) := by
  intro a b
  simp only [complexPureGauge]
  ring

@[simp] theorem tensorRe_add (k l : ComplexTensor2) : tensorRe (k + l) = tensorRe k + tensorRe l := by
  funext a b
  simp [tensorRe]

@[simp] theorem tensorIm_add (k l : ComplexTensor2) : tensorIm (k + l) = tensorIm k + tensorIm l := by
  funext a b
  simp [tensorIm]

theorem complexRicciSymbol_add (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2)
    (a b : Index) :
    complexRicciSymbol gInv ξ (k + l) a b =
      complexRicciSymbol gInv ξ k a b + complexRicciSymbol gInv ξ l a b := by
  apply Complex.ext
  · simp [complexRicciSymbol_re, ricciSymbol_add]
  · simp [complexRicciSymbol_im, ricciSymbol_add]

/-- Changing the second representative by any complex gauge vector preserves
the original Hermitian physical pairing against a null-kernel amplitude. -/
theorem hermitianPhysicalPairing_add_pureGauge_right
    (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2) (v : ComplexCovector)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricComplexTensor k)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0) :
    hermitianPhysicalPairing gInv k (l + complexPureGauge ξ v) = hermitianPhysicalPairing gInv k l := by
  rw [hermitianPhysicalPairing_add_right gInv k l (complexPureGauge ξ v) hg,
    hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ k v hg hkSymm hξ hs hk,
    add_zero]

theorem hermitianPhysicalPairing_add_pureGauge_left
    (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2) (v : ComplexCovector)
    (hg : IsSymmetricTensor gInv) (hlSymm : IsSymmetricComplexTensor l)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) :
    hermitianPhysicalPairing gInv (k + complexPureGauge ξ v) l = hermitianPhysicalPairing gInv k l := by
  rw [hermitianPhysicalPairing_add_left,
    hermitianPhysicalPairing_conj_symm gInv (complexPureGauge ξ v) l hg,
    hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ l v hg hlSymm hξ hs hl]
  simp

/-- Both representatives may be changed independently on the same null kernel. -/
theorem hermitianPhysicalPairing_add_pureGauge_both
    (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2) (v w : ComplexCovector)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricComplexTensor k)
    (hlSymm : IsSymmetricComplexTensor l) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) :
    hermitianPhysicalPairing gInv (k + complexPureGauge ξ v) (l + complexPureGauge ξ w) =
      hermitianPhysicalPairing gInv k l := by
  have hlS : IsSymmetricComplexTensor (l + complexPureGauge ξ w) := by
    intro a b
    change l a b + complexPureGauge ξ w a b = l b a + complexPureGauge ξ w b a
    rw [hlSymm a b, complexPureGauge_symmetric ξ w a b]
  have hlK : ∀ a b, complexRicciSymbol gInv ξ (l + complexPureGauge ξ w) a b = 0 := by
    intro a b
    rw [complexRicciSymbol_add, hl a b, complexRicciSymbol_pureGauge_eq_zero gInv ξ w hg, add_zero]
  rw [hermitianPhysicalPairing_add_pureGauge_left gInv ξ k _ v hg hlS hξ hs hlK,
    hermitianPhysicalPairing_add_pureGauge_right gInv ξ k l w hg hkSymm hξ hs hk]

namespace HermitianScreen

open NullScreen

/-- In the standard Lorentz/null coordinates, the original Hermitian physical
form equals the ordinary two-complex-component screen pairing. -/
theorem hermitianPhysicalPairing_eq_screen (k l : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k) (hlSymm : IsSymmetricComplexTensor l)
    (hk : ∀ a b, complexRicciSymbol minkowskiInverse nullCovector k a b = 0)
    (hl : ∀ a b, complexRicciSymbol minkowskiInverse nullCovector l a b = 0) :
    hermitianPhysicalPairing minkowskiInverse k l =
      2 * (k 2 2 * conj (l 2 2) + k 2 3 * conj (l 2 3)) := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff minkowskiInverse nullCovector k).mp hk
  obtain ⟨hlr, hli⟩ := (complexRicci_kernel_iff minkowskiInverse nullCovector l).mp hl
  have hkrS := tensorRe_symmetric k hkSymm
  have hkiS := tensorIm_symmetric k hkSymm
  have hlrS := tensorRe_symmetric l hlSymm
  have hliS := tensorIm_symmetric l hlSymm
  apply Complex.ext
  · rw [hermitianPhysicalPairing_re,
      physicalPairing_eq_screen _ _ hkrS hlrS hkr hlr,
      physicalPairing_eq_screen _ _ hkiS hliS hki hli]
    simp [tensorRe, tensorIm, Complex.mul_re, Complex.mul_im]
    ring
  · rw [hermitianPhysicalPairing_im,
      physicalPairing_eq_screen _ _ hkiS hlrS hki hlr,
      physicalPairing_eq_screen _ _ hkrS hliS hkr hli]
    simp [tensorRe, tensorIm, Complex.mul_re, Complex.mul_im]
    ring

theorem hermitianPhysicalPairing_self_eq_screen (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k)
    (hk : ∀ a b, complexRicciSymbol minkowskiInverse nullCovector k a b = 0) :
    hermitianPhysicalPairing minkowskiInverse k k =
      ((2 * (Complex.normSq (k 2 2) + Complex.normSq (k 2 3)) : ℝ) : ℂ) := by
  rw [hermitianPhysicalPairing_eq_screen k k hkSymm hkSymm hk hk,
    Complex.mul_conj, Complex.mul_conj]
  simp

/-- Nonnegativity is stated in ℝ via the real part; the complex diagonal is
proved real separately. Neither positivity nor a screen formula is assumed. -/
theorem hermitianPhysicalPairing_self_re_nonneg (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k)
    (hk : ∀ a b, complexRicciSymbol minkowskiInverse nullCovector k a b = 0) :
    0 ≤ (hermitianPhysicalPairing minkowskiInverse k k).re := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff minkowskiInverse nullCovector k).mp hk
  rw [hermitianPhysicalPairing_diag_re]
  exact add_nonneg
    (physicalPairing_self_nonneg _ (tensorRe_symmetric k hkSymm) hkr)
    (physicalPairing_self_nonneg _ (tensorIm_symmetric k hkSymm) hki)

theorem hermitianPhysicalPairing_self_im_eq_zero (k : ComplexTensor2) :
    (hermitianPhysicalPairing minkowskiInverse k k).im = 0 :=
  hermitianPhysicalPairing_diag_im minkowskiInverse k minkowskiInverse_symmetric

/-- The null space of the positive complex screen form is exactly the actual
complex pure gauge tensors, with an explicitly constructed complex gauge vector. -/
theorem hermitianPhysicalPairing_self_eq_zero_iff_pureGauge (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k)
    (hk : ∀ a b, complexRicciSymbol minkowskiInverse nullCovector k a b = 0) :
    hermitianPhysicalPairing minkowskiInverse k k = 0 ↔
      ∃ v : ComplexCovector, k = complexPureGauge nullCovector v := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff minkowskiInverse nullCovector k).mp hk
  have hkrS := tensorRe_symmetric k hkSymm
  have hkiS := tensorIm_symmetric k hkSymm
  constructor
  · intro hz
    have hzR : physicalPairing minkowskiInverse (tensorRe k) (tensorRe k) +
        physicalPairing minkowskiInverse (tensorIm k) (tensorIm k) = 0 := by
      simpa only [hermitianPhysicalPairing_diag_re, Complex.zero_re] using congrArg Complex.re hz
    have hrr := physicalPairing_self_nonneg _ hkrS hkr
    have hii := physicalPairing_self_nonneg _ hkiS hki
    have hzkr : physicalPairing minkowskiInverse (tensorRe k) (tensorRe k) = 0 := by linarith
    have hzki : physicalPairing minkowskiInverse (tensorIm k) (tensorIm k) = 0 := by linarith
    obtain ⟨vr, hvr⟩ := (physicalPairing_self_eq_zero_iff_pureGauge _ hkrS hkr).mp hzkr
    obtain ⟨vi, hvi⟩ := (physicalPairing_self_eq_zero_iff_pureGauge _ hkiS hki).mp hzki
    refine ⟨fun a => (vr a : ℂ) + (vi a : ℂ) * Complex.I, ?_⟩
    funext a b
    apply Complex.ext
    · simpa [tensorRe, complexPureGauge, pureGauge, Complex.mul_re, Complex.mul_im] using
        congrFun (congrFun hvr a) b
    · simpa [tensorIm, complexPureGauge, pureGauge, Complex.mul_re, Complex.mul_im] using
        congrFun (congrFun hvi a) b
  · rintro ⟨v, hv⟩
    calc
      hermitianPhysicalPairing minkowskiInverse k k =
          hermitianPhysicalPairing minkowskiInverse k (complexPureGauge nullCovector v) := by rw [← hv]
      _ = 0 := hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel
        minkowskiInverse nullCovector k v minkowskiInverse_symmetric hkSymm
        nullCovector_ne_zero nullCovector_symbolNorm hk

/-- Every pair of complex screen coordinates is realized by an actual complex
symmetric Ricci-kernel amplitude. -/
def complexScreenTensor (a b : ℂ) : ComplexTensor2 :=
  tensorOfReal (screenTensor a.re b.re) + Complex.I • tensorOfReal (screenTensor a.im b.im)

@[simp] theorem tensorRe_complexScreenTensor (a b : ℂ) :
    tensorRe (complexScreenTensor a b) = screenTensor a.re b.re := by
  funext i j
  simp [complexScreenTensor, tensorRe, tensorOfReal, Pi.smul_apply, smul_eq_mul,
    Complex.mul_re]

@[simp] theorem tensorIm_complexScreenTensor (a b : ℂ) :
    tensorIm (complexScreenTensor a b) = screenTensor a.im b.im := by
  funext i j
  simp [complexScreenTensor, tensorIm, tensorOfReal, Pi.smul_apply, smul_eq_mul,
    Complex.mul_im]

theorem complexScreenTensor_symmetric (a b : ℂ) :
    IsSymmetricComplexTensor (complexScreenTensor a b) := by
  intro i j
  apply Complex.ext
  · have h := screenTensor_symmetric a.re b.re i j
    simpa only [← tensorRe_complexScreenTensor a b] using h
  · have h := screenTensor_symmetric a.im b.im i j
    simpa only [← tensorIm_complexScreenTensor a b] using h

theorem complexScreenTensor_kernel (a b : ℂ) :
    ∀ i j, complexRicciSymbol minkowskiInverse nullCovector (complexScreenTensor a b) i j = 0 := by
  apply (complexRicci_kernel_iff minkowskiInverse nullCovector (complexScreenTensor a b)).mpr
  constructor
  · simpa only [tensorRe_complexScreenTensor] using screenTensor_kernel a.re b.re
  · simpa only [tensorIm_complexScreenTensor] using screenTensor_kernel a.im b.im

@[simp] theorem complexScreenTensor_22 (a b : ℂ) : complexScreenTensor a b 2 2 = a := by
  apply Complex.ext <;>
    simp [complexScreenTensor, tensorOfReal, screenTensor, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im]

@[simp] theorem complexScreenTensor_23 (a b : ℂ) : complexScreenTensor a b 2 3 = b := by
  apply Complex.ext <;>
    simp [complexScreenTensor, tensorOfReal, screenTensor, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im]

theorem complexScreenTensor_pairing (a b c d : ℂ) :
    hermitianPhysicalPairing minkowskiInverse (complexScreenTensor a b) (complexScreenTensor c d) =
      2 * (a * conj c + b * conj d) := by
  rw [hermitianPhysicalPairing_eq_screen _ _ (complexScreenTensor_symmetric a b)
    (complexScreenTensor_symmetric c d) (complexScreenTensor_kernel a b) (complexScreenTensor_kernel c d)]
  simp

theorem complexScreenTensor_self_pairing (a b : ℂ) :
    hermitianPhysicalPairing minkowskiInverse (complexScreenTensor a b) (complexScreenTensor a b) =
      ((2 * (Complex.normSq a + Complex.normSq b) : ℝ) : ℂ) := by
  rw [hermitianPhysicalPairing_self_eq_screen _ (complexScreenTensor_symmetric a b)
    (complexScreenTensor_kernel a b)]
  simp

def complexGaugeVector (k : ComplexTensor2) : ComplexCovector := fun a =>
  (gaugeVector (tensorRe k) a : ℂ) + (gaugeVector (tensorIm k) a : ℂ) * Complex.I

/-- The actual kernel amplitudes have exactly two free complex screen
coordinates modulo an explicitly recovered gauge representative. -/
theorem complex_kernel_decomposition (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k)
    (hk : ∀ a b, complexRicciSymbol minkowskiInverse nullCovector k a b = 0) :
    k = complexPureGauge nullCovector (complexGaugeVector k) +
      complexScreenTensor (k 2 2) (k 2 3) := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff minkowskiInverse nullCovector k).mp hk
  have hr := kernel_decomposition (tensorRe k) (tensorRe_symmetric k hkSymm) hkr
  have hi := kernel_decomposition (tensorIm k) (tensorIm_symmetric k hkSymm) hki
  funext a b
  apply Complex.ext
  · simpa [tensorRe, tensorIm, complexPureGauge, complexGaugeVector, complexScreenTensor,
      pureGauge, tensorOfReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] using congrFun (congrFun hr a) b
  · simpa [tensorRe, tensorIm, complexPureGauge, complexGaugeVector, complexScreenTensor,
      pureGauge, tensorOfReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Complex.mul_re, Complex.mul_im] using congrFun (congrFun hi a) b

end HermitianScreen

end Burnett.RicciSymbol
