import Burnett.Algebra.RealPolarization
import Mathlib.Data.Complex.Basic

noncomputable section

namespace Burnett.RicciSymbol

open scoped BigOperators ComplexConjugate

/-- Complex amplitudes over the same four real coordinate indices. -/
abbrev ComplexTensor2 := Index → Index → ℂ

def tensorRe (k : ComplexTensor2) : Tensor2 := fun a b => (k a b).re
def tensorIm (k : ComplexTensor2) : Tensor2 := fun a b => (k a b).im
def tensorConj (k : ComplexTensor2) : ComplexTensor2 := fun a b => conj (k a b)
def tensorOfReal (k : Tensor2) : ComplexTensor2 := fun a b => (k a b : ℂ)

abbrev ComplexCovector := Index → ℂ

def complexPureGauge (ξ : Covector) (v : ComplexCovector) : ComplexTensor2 :=
  fun a b => (ξ a : ℂ) * v b + v a * (ξ b : ℂ)

def IsSymmetricComplexTensor (k : ComplexTensor2) : Prop := ∀ a b, k a b = k b a

private theorem cp_re_sum (f : Index → ℂ) : (∑ a, f a).re = ∑ a, (f a).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

private theorem cp_im_sum (f : Index → ℂ) : (∑ a, f a).im = ∑ a, (f a).im :=
  map_sum Complex.imAddGroupHom f Finset.univ

/-- The trace with the original real inverse metric and a complex amplitude. -/
def complexMetricTrace (gInv : Tensor2) (k : ComplexTensor2) : ℂ :=
  ∑ a, ∑ b, (gInv a b : ℂ) * k a b

def complexContracted (gInv : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (b : Index) : ℂ :=
  ∑ a, (raiseCovector gInv ξ a : ℂ) * k a b

def complexRaiseSecond (gInv : Tensor2) (k : ComplexTensor2) (c a : Index) : ℂ :=
  ∑ d, (gInv a d : ℂ) * k c d

/-- Complexification of the actual Ricci symbol, not a new kernel assumption. -/
def complexRicciSymbol (gInv : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (a b : Index) : ℂ :=
  ((symbolNorm gInv ξ : ℂ) * k a b + (ξ a : ℂ) * ξ b * complexMetricTrace gInv k -
    (ξ a : ℂ) * complexContracted gInv ξ k b -
    (ξ b : ℂ) * complexContracted gInv ξ k a) / 2

/-- The paper's connection symbol with complex amplitude and real metric/frequency. -/
def complexConnectionSymbol (gInv : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (a b c : Index) : ℂ :=
  ((ξ b : ℂ) * complexRaiseSecond gInv k c a +
    (ξ c : ℂ) * complexRaiseSecond gInv k b a -
    (raiseCovector gInv ξ a : ℂ) * k b c) / 2

def complexConnectionCross (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2)
    (b c : Index) : ℂ :=
  ∑ a, ∑ e,
    (complexConnectionSymbol gInv ξ k a c e * complexConnectionSymbol gInv ξ l e b a -
      complexConnectionSymbol gInv ξ k a a e * complexConnectionSymbol gInv ξ l e b c)

/-- Hermitian polarization of the original connection products, linear in the
first amplitude, as required by the paper's inner-product convention. -/
def hermitianQuadraticSymbol (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2)
    (b c : Index) : ℂ :=
  (complexConnectionCross gInv ξ k (tensorConj l) b c +
    complexConnectionCross gInv ξ (tensorConj l) k b c) / 2

/-- The original full ordered contraction, conjugate-linear in its second slot. -/
def hermitianPhysicalPairing (gInv : Tensor2) (k l : ComplexTensor2) : ℂ :=
  (∑ a, ∑ b, ∑ c, ∑ d,
    (gInv a c : ℂ) * gInv b d * k a b * conj (l c d)) -
    complexMetricTrace gInv k * conj (complexMetricTrace gInv l) / 2

@[simp] theorem complexMetricTrace_re (gInv : Tensor2) (k : ComplexTensor2) :
    (complexMetricTrace gInv k).re = metricTrace gInv (tensorRe k) := by
  simp [complexMetricTrace, metricTrace, tensorRe, cp_re_sum, Complex.mul_re]

@[simp] theorem complexMetricTrace_im (gInv : Tensor2) (k : ComplexTensor2) :
    (complexMetricTrace gInv k).im = metricTrace gInv (tensorIm k) := by
  simp [complexMetricTrace, metricTrace, tensorIm, cp_im_sum, Complex.mul_im]

@[simp] theorem complexContracted_re (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (b : Index) :
    (complexContracted gInv ξ k b).re = contracted gInv ξ (tensorRe k) b := by
  simp [complexContracted, contracted, tensorRe, cp_re_sum, Complex.mul_re]

@[simp] theorem complexContracted_im (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (b : Index) :
    (complexContracted gInv ξ k b).im = contracted gInv ξ (tensorIm k) b := by
  simp [complexContracted, contracted, tensorIm, cp_im_sum, Complex.mul_im]

@[simp] theorem complexRaiseSecond_re (gInv : Tensor2) (k : ComplexTensor2) (c a : Index) :
    (complexRaiseSecond gInv k c a).re = raiseSecond gInv (tensorRe k) c a := by
  simp [complexRaiseSecond, raiseSecond, tensorRe, cp_re_sum, Complex.mul_re]

@[simp] theorem complexRaiseSecond_im (gInv : Tensor2) (k : ComplexTensor2) (c a : Index) :
    (complexRaiseSecond gInv k c a).im = raiseSecond gInv (tensorIm k) c a := by
  simp [complexRaiseSecond, raiseSecond, tensorIm, cp_im_sum, Complex.mul_im]

@[simp] theorem complexRicciSymbol_re (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (a b : Index) :
    (complexRicciSymbol gInv ξ k a b).re = ricciSymbol gInv ξ (tensorRe k) a b := by
  simp [complexRicciSymbol, ricciSymbol, tensorRe, Complex.mul_re]

@[simp] theorem complexRicciSymbol_im (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (a b : Index) :
    (complexRicciSymbol gInv ξ k a b).im = ricciSymbol gInv ξ (tensorIm k) a b := by
  simp [complexRicciSymbol, ricciSymbol, tensorIm, Complex.mul_im]

/-- The complex kernel has exactly the two real kernel conditions; no extra
analytic or geometric assumption is inserted by complexification. -/
theorem complexRicci_kernel_iff (gInv : Tensor2) (ξ : Covector) (k : ComplexTensor2) :
    (∀ a b, complexRicciSymbol gInv ξ k a b = 0) ↔
      (∀ a b, ricciSymbol gInv ξ (tensorRe k) a b = 0) ∧
      (∀ a b, ricciSymbol gInv ξ (tensorIm k) a b = 0) := by
  constructor
  · intro h
    constructor
    · intro a b
      simpa using congrArg Complex.re (h a b)
    · intro a b
      simpa using congrArg Complex.im (h a b)
  · rintro ⟨hr, hi⟩ a b
    apply Complex.ext
    · simpa using hr a b
    · simpa using hi a b

@[simp] theorem complexConnectionSymbol_re (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (a b c : Index) :
    (complexConnectionSymbol gInv ξ k a b c).re =
      connectionSymbol gInv ξ (tensorRe k) a b c := by
  simp [complexConnectionSymbol, connectionSymbol, tensorRe, Complex.mul_re]

@[simp] theorem complexConnectionSymbol_im (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (a b c : Index) :
    (complexConnectionSymbol gInv ξ k a b c).im =
      connectionSymbol gInv ξ (tensorIm k) a b c := by
  simp [complexConnectionSymbol, connectionSymbol, tensorIm, Complex.mul_im]

theorem complexConnectionCross_re (gInv : Tensor2) (ξ : Covector)
    (k l : ComplexTensor2) (b c : Index) :
    (complexConnectionCross gInv ξ k l b c).re =
      connectionCrossSymbol gInv ξ (tensorRe k) (tensorRe l) b c -
      connectionCrossSymbol gInv ξ (tensorIm k) (tensorIm l) b c := by
  simp only [complexConnectionCross, cp_re_sum, Complex.sub_re, Complex.mul_re,
    complexConnectionSymbol_re, complexConnectionSymbol_im, connectionCrossSymbol,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem complexConnectionCross_im (gInv : Tensor2) (ξ : Covector)
    (k l : ComplexTensor2) (b c : Index) :
    (complexConnectionCross gInv ξ k l b c).im =
      connectionCrossSymbol gInv ξ (tensorRe k) (tensorIm l) b c +
      connectionCrossSymbol gInv ξ (tensorIm k) (tensorRe l) b c := by
  simp only [complexConnectionCross, cp_im_sum, Complex.sub_im, Complex.mul_im,
    complexConnectionSymbol_re, complexConnectionSymbol_im, connectionCrossSymbol,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

@[simp] theorem tensorRe_conj (k : ComplexTensor2) : tensorRe (tensorConj k) = tensorRe k := by
  funext a b
  simp [tensorRe, tensorConj]

@[simp] theorem tensorIm_conj (k : ComplexTensor2) : tensorIm (tensorConj k) = (-1 : ℝ) • tensorIm k := by
  funext a b
  simp [tensorIm, tensorConj]

/-- Reconstructed from the actual complex connection products. -/
theorem hermitianQuadraticSymbol_re (gInv : Tensor2) (ξ : Covector)
    (k l : ComplexTensor2) (b c : Index) :
    (hermitianQuadraticSymbol gInv ξ k l b c).re =
      mixedQuadraticSymbol gInv ξ (tensorRe k) (tensorRe l) b c +
      mixedQuadraticSymbol gInv ξ (tensorIm k) (tensorIm l) b c := by
  simp [hermitianQuadraticSymbol, complexConnectionCross_re,
    connectionCrossSymbol_smul_left, connectionCrossSymbol_smul_right,
    mixedQuadraticSymbol]
  ring

theorem hermitianQuadraticSymbol_im (gInv : Tensor2) (ξ : Covector)
    (k l : ComplexTensor2) (b c : Index) :
    (hermitianQuadraticSymbol gInv ξ k l b c).im =
      mixedQuadraticSymbol gInv ξ (tensorIm k) (tensorRe l) b c -
      mixedQuadraticSymbol gInv ξ (tensorRe k) (tensorIm l) b c := by
  simp [hermitianQuadraticSymbol, complexConnectionCross_im,
    connectionCrossSymbol_smul_left, connectionCrossSymbol_smul_right,
    mixedQuadraticSymbol]
  ring

theorem hermitianPhysicalPairing_re (gInv : Tensor2) (k l : ComplexTensor2) :
    (hermitianPhysicalPairing gInv k l).re =
      physicalPairing gInv (tensorRe k) (tensorRe l) +
      physicalPairing gInv (tensorIm k) (tensorIm l) := by
  simp [hermitianPhysicalPairing, physicalPairing, tensorPairing, tensorRe, tensorIm,
    cp_re_sum, Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib]
  ring

theorem hermitianPhysicalPairing_im (gInv : Tensor2) (k l : ComplexTensor2) :
    (hermitianPhysicalPairing gInv k l).im =
      physicalPairing gInv (tensorIm k) (tensorRe l) -
      physicalPairing gInv (tensorRe k) (tensorIm l) := by
  simp [hermitianPhysicalPairing, physicalPairing, tensorPairing, tensorRe, tensorIm,
    cp_im_sum, Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

/-- Conjugate symmetry exchanges amplitudes, not coordinate indices. -/
theorem hermitianQuadraticSymbol_conj_symm (gInv : Tensor2) (ξ : Covector)
    (k l : ComplexTensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ k l b c =
      conj (hermitianQuadraticSymbol gInv ξ l k b c) := by
  apply Complex.ext
  · simp only [hermitianQuadraticSymbol_re, Complex.conj_re]
    rw [mixedQuadraticSymbol_comm gInv ξ (tensorRe l) (tensorRe k),
      mixedQuadraticSymbol_comm gInv ξ (tensorIm l) (tensorIm k)]
  · simp only [hermitianQuadraticSymbol_im, Complex.conj_im]
    rw [mixedQuadraticSymbol_comm gInv ξ (tensorIm l) (tensorRe k),
      mixedQuadraticSymbol_comm gInv ξ (tensorRe l) (tensorIm k)]
    ring

theorem hermitianPhysicalPairing_conj_symm (gInv : Tensor2) (k l : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) :
    hermitianPhysicalPairing gInv k l = conj (hermitianPhysicalPairing gInv l k) := by
  apply Complex.ext
  · simp only [hermitianPhysicalPairing_re, Complex.conj_re]
    rw [physicalPairing_comm gInv (tensorRe l) (tensorRe k) hg,
      physicalPairing_comm gInv (tensorIm l) (tensorIm k) hg]
  · simp only [hermitianPhysicalPairing_im, Complex.conj_im]
    rw [physicalPairing_comm gInv (tensorIm l) (tensorRe k) hg,
      physicalPairing_comm gInv (tensorRe l) (tensorIm k) hg]
    ring

@[simp] theorem tensorRe_ofReal (k : Tensor2) : tensorRe (tensorOfReal k) = k := by
  funext a b
  simp [tensorRe, tensorOfReal]

@[simp] theorem tensorIm_ofReal (k : Tensor2) : tensorIm (tensorOfReal k) = 0 := by
  funext a b
  simp [tensorIm, tensorOfReal]

private theorem cp_mixed_zero_left (gInv : Tensor2) (ξ : Covector) (k : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ 0 k b c = 0 := by
  have hz : (0 : ℝ) • (0 : Tensor2) = 0 := by funext a b; simp
  simpa only [hz, zero_mul] using
    mixedQuadraticSymbol_smul_left gInv ξ 0 (0 : Tensor2) k b c

private theorem cp_mixed_zero_right (gInv : Tensor2) (ξ : Covector) (k : Tensor2) (b c : Index) :
    mixedQuadraticSymbol gInv ξ k 0 b c = 0 := by
  have hz : (0 : ℝ) • (0 : Tensor2) = 0 := by funext a b; simp
  simpa only [hz, zero_mul] using
    mixedQuadraticSymbol_smul_right gInv ξ 0 k (0 : Tensor2) b c

private theorem cp_physical_zero_left (gInv k : Tensor2) : physicalPairing gInv 0 k = 0 := by
  have hz : (0 : ℝ) • (0 : Tensor2) = 0 := by funext a b; simp
  simpa only [hz, zero_mul] using physicalPairing_smul_left gInv 0 (0 : Tensor2) k

private theorem cp_physical_zero_right (gInv k : Tensor2) : physicalPairing gInv k 0 = 0 := by
  have hz : (0 : ℝ) • (0 : Tensor2) = 0 := by funext a b; simp
  simpa only [hz, zero_mul] using physicalPairing_smul_right gInv 0 k (0 : Tensor2)

/-- The complex connection-product form restricts to the already proved real
mixed form, with no change of normalization. -/
theorem hermitianQuadraticSymbol_ofReal (gInv : Tensor2) (ξ : Covector)
    (k l : Tensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ (tensorOfReal k) (tensorOfReal l) b c =
      (mixedQuadraticSymbol gInv ξ k l b c : ℂ) := by
  apply Complex.ext
  · simp [hermitianQuadraticSymbol_re, cp_mixed_zero_left]
  · simp [hermitianQuadraticSymbol_im, cp_mixed_zero_left, cp_mixed_zero_right]

theorem hermitianQuadraticSymbol_real_diagonal (gInv : Tensor2) (ξ : Covector)
    (k : Tensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ (tensorOfReal k) (tensorOfReal k) b c =
      (quadraticSymbol gInv ξ k b c : ℂ) := by
  rw [hermitianQuadraticSymbol_ofReal, mixedQuadraticSymbol_diag]

theorem hermitianPhysicalPairing_ofReal (gInv k l : Tensor2) :
    hermitianPhysicalPairing gInv (tensorOfReal k) (tensorOfReal l) =
      (physicalPairing gInv k l : ℂ) := by
  apply Complex.ext
  · simp [hermitianPhysicalPairing_re, cp_physical_zero_left]
  · simp [hermitianPhysicalPairing_im, cp_physical_zero_left, cp_physical_zero_right]

/-- A diagonal complex amplitude contributes the sum of the two original real
quadratic expressions; this identity is not used as the definition. -/
theorem hermitianQuadraticSymbol_diag_re (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (b c : Index) :
    (hermitianQuadraticSymbol gInv ξ k k b c).re =
      quadraticSymbol gInv ξ (tensorRe k) b c +
      quadraticSymbol gInv ξ (tensorIm k) b c := by
  rw [hermitianQuadraticSymbol_re, mixedQuadraticSymbol_diag, mixedQuadraticSymbol_diag]

theorem hermitianQuadraticSymbol_diag_im (gInv : Tensor2) (ξ : Covector)
    (k : ComplexTensor2) (b c : Index) :
    (hermitianQuadraticSymbol gInv ξ k k b c).im = 0 := by
  rw [hermitianQuadraticSymbol_im,
    mixedQuadraticSymbol_comm gInv ξ (tensorIm k) (tensorRe k), sub_self]

theorem hermitianPhysicalPairing_diag_re (gInv : Tensor2) (k : ComplexTensor2) :
    (hermitianPhysicalPairing gInv k k).re =
      physicalPairing gInv (tensorRe k) (tensorRe k) +
      physicalPairing gInv (tensorIm k) (tensorIm k) :=
  hermitianPhysicalPairing_re gInv k k

theorem hermitianPhysicalPairing_diag_im (gInv : Tensor2) (k : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) :
    (hermitianPhysicalPairing gInv k k).im = 0 := by
  rw [hermitianPhysicalPairing_im,
    physicalPairing_comm gInv (tensorIm k) (tensorRe k) hg, sub_self]

/-- Every mixed Hermitian term vanishes off the characteristic cone. -/
theorem hermitianQuadraticSymbol_eq_zero_of_noncharacteristic_kernel
    (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2)
    (hs : symbolNorm gInv ξ ≠ 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ k l b c = 0 := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff gInv ξ k).mp hk
  obtain ⟨hlr, hli⟩ := (complexRicci_kernel_iff gInv ξ l).mp hl
  apply Complex.ext
  · rw [hermitianQuadraticSymbol_re,
      mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ _ _ hs hkr hlr,
      mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ _ _ hs hki hli]
    simp
  · rw [hermitianQuadraticSymbol_im,
      mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ _ _ hs hki hlr,
      mixedQuadraticSymbol_eq_zero_of_noncharacteristic_kernel gInv ξ _ _ hs hkr hli]
    simp

theorem tensorRe_symmetric (k : ComplexTensor2) (hk : IsSymmetricComplexTensor k) :
    IsSymmetricTensor (tensorRe k) := by
  intro a b
  exact congrArg Complex.re (hk a b)

theorem tensorIm_symmetric (k : ComplexTensor2) (hk : IsSymmetricComplexTensor k) :
    IsSymmetricTensor (tensorIm k) := by
  intro a b
  exact congrArg Complex.im (hk a b)

@[simp] theorem tensorRe_complexPureGauge (ξ : Covector) (v : ComplexCovector) :
    tensorRe (complexPureGauge ξ v) = pureGauge ξ (fun a => (v a).re) := by
  funext a b
  simp [tensorRe, complexPureGauge, pureGauge, Complex.mul_re]

@[simp] theorem tensorIm_complexPureGauge (ξ : Covector) (v : ComplexCovector) :
    tensorIm (complexPureGauge ξ v) = pureGauge ξ (fun a => (v a).im) := by
  funext a b
  simp [tensorIm, complexPureGauge, pureGauge, Complex.mul_im]

/-- Physical/gauge cancellation holds for every complex gauge vector, not only
for a real or diagonal gauge amplitude. -/
theorem hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel
    (gInv : Tensor2) (ξ : Covector) (k : ComplexTensor2) (v : ComplexCovector)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricComplexTensor k)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0) :
    hermitianPhysicalPairing gInv k (complexPureGauge ξ v) = 0 := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff gInv ξ k).mp hk
  have hkrS := tensorRe_symmetric k hkSymm
  have hkiS := tensorIm_symmetric k hkSymm
  apply Complex.ext
  · rw [hermitianPhysicalPairing_re, tensorRe_complexPureGauge, tensorIm_complexPureGauge,
      physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ _ _ hg hkrS hξ hs hkr,
      physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ _ _ hg hkiS hξ hs hki]
    simp
  · rw [hermitianPhysicalPairing_im, tensorRe_complexPureGauge, tensorIm_complexPureGauge,
      physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ _ _ hg hkiS hξ hs hki,
      physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ _ _ hg hkrS hξ hs hkr]
    simp

theorem complexRaiseSecond_add (gInv : Tensor2) (k l : ComplexTensor2) (c a : Index) :
    complexRaiseSecond gInv (k + l) c a =
      complexRaiseSecond gInv k c a + complexRaiseSecond gInv l c a := by
  simp [complexRaiseSecond, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem complexRaiseSecond_smul (gInv : Tensor2) (z : ℂ) (k : ComplexTensor2) (c a : Index) :
    complexRaiseSecond gInv (z • k) c a = z * complexRaiseSecond gInv k c a := by
  simp only [complexRaiseSecond, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem complexConnectionSymbol_add (gInv : Tensor2) (ξ : Covector)
    (k l : ComplexTensor2) (a b c : Index) :
    complexConnectionSymbol gInv ξ (k + l) a b c =
      complexConnectionSymbol gInv ξ k a b c + complexConnectionSymbol gInv ξ l a b c := by
  simp only [complexConnectionSymbol, complexRaiseSecond_add, Pi.add_apply]
  ring

theorem complexConnectionSymbol_smul (gInv : Tensor2) (ξ : Covector)
    (z : ℂ) (k : ComplexTensor2) (a b c : Index) :
    complexConnectionSymbol gInv ξ (z • k) a b c =
      z * complexConnectionSymbol gInv ξ k a b c := by
  simp only [complexConnectionSymbol, complexRaiseSecond_smul, Pi.smul_apply, smul_eq_mul]
  ring

theorem complexConnectionCross_add_left (gInv : Tensor2) (ξ : Covector)
    (k l m : ComplexTensor2) (b c : Index) :
    complexConnectionCross gInv ξ (k + l) m b c =
      complexConnectionCross gInv ξ k m b c + complexConnectionCross gInv ξ l m b c := by
  simp only [complexConnectionCross, complexConnectionSymbol_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem complexConnectionCross_add_right (gInv : Tensor2) (ξ : Covector)
    (k l m : ComplexTensor2) (b c : Index) :
    complexConnectionCross gInv ξ k (l + m) b c =
      complexConnectionCross gInv ξ k l b c + complexConnectionCross gInv ξ k m b c := by
  simp only [complexConnectionCross, complexConnectionSymbol_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem complexConnectionCross_smul_left (gInv : Tensor2) (ξ : Covector)
    (z : ℂ) (k l : ComplexTensor2) (b c : Index) :
    complexConnectionCross gInv ξ (z • k) l b c =
      z * complexConnectionCross gInv ξ k l b c := by
  simp only [complexConnectionCross, complexConnectionSymbol_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem complexConnectionCross_smul_right (gInv : Tensor2) (ξ : Covector)
    (z : ℂ) (k l : ComplexTensor2) (b c : Index) :
    complexConnectionCross gInv ξ k (z • l) b c =
      z * complexConnectionCross gInv ξ k l b c := by
  simp only [complexConnectionCross, complexConnectionSymbol_smul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem hermitianQuadraticSymbol_add_left (gInv : Tensor2) (ξ : Covector)
    (k l m : ComplexTensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ (k + l) m b c =
      hermitianQuadraticSymbol gInv ξ k m b c + hermitianQuadraticSymbol gInv ξ l m b c := by
  simp only [hermitianQuadraticSymbol, complexConnectionCross_add_left, complexConnectionCross_add_right]
  ring

theorem hermitianQuadraticSymbol_smul_left (gInv : Tensor2) (ξ : Covector)
    (z : ℂ) (k l : ComplexTensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ (z • k) l b c =
      z * hermitianQuadraticSymbol gInv ξ k l b c := by
  simp only [hermitianQuadraticSymbol, complexConnectionCross_smul_left, complexConnectionCross_smul_right]
  ring

theorem hermitianQuadraticSymbol_add_right (gInv : Tensor2) (ξ : Covector)
    (k l m : ComplexTensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ k (l + m) b c =
      hermitianQuadraticSymbol gInv ξ k l b c + hermitianQuadraticSymbol gInv ξ k m b c := by
  have hc : tensorConj (l + m) = tensorConj l + tensorConj m := by
    funext a b
    simp [tensorConj, Pi.add_apply]
  simp only [hermitianQuadraticSymbol, hc, complexConnectionCross_add_left, complexConnectionCross_add_right]
  ring

theorem hermitianQuadraticSymbol_smul_right (gInv : Tensor2) (ξ : Covector)
    (z : ℂ) (k l : ComplexTensor2) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ k (z • l) b c =
      conj z * hermitianQuadraticSymbol gInv ξ k l b c := by
  have hc : tensorConj (z • l) = conj z • tensorConj l := by
    funext a b
    simp [tensorConj, Pi.smul_apply, smul_eq_mul, map_mul]
  simp only [hermitianQuadraticSymbol, hc, complexConnectionCross_smul_left, complexConnectionCross_smul_right]
  ring

theorem complexMetricTrace_add (gInv : Tensor2) (k l : ComplexTensor2) :
    complexMetricTrace gInv (k + l) = complexMetricTrace gInv k + complexMetricTrace gInv l := by
  simp [complexMetricTrace, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem complexMetricTrace_smul (gInv : Tensor2) (z : ℂ) (k : ComplexTensor2) :
    complexMetricTrace gInv (z • k) = z * complexMetricTrace gInv k := by
  simp only [complexMetricTrace, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem hermitianPhysicalPairing_add_left (gInv : Tensor2) (k l m : ComplexTensor2) :
    hermitianPhysicalPairing gInv (k + l) m =
      hermitianPhysicalPairing gInv k m + hermitianPhysicalPairing gInv l m := by
  simp only [hermitianPhysicalPairing, complexMetricTrace_add, Pi.add_apply,
    add_mul, mul_add, Finset.sum_add_distrib]
  ring

theorem hermitianPhysicalPairing_smul_left (gInv : Tensor2) (z : ℂ) (k l : ComplexTensor2) :
    hermitianPhysicalPairing gInv (z • k) l = z * hermitianPhysicalPairing gInv k l := by
  have hsum :
      (∑ a, ∑ b, ∑ c, ∑ d,
        (gInv a c : ℂ) * gInv b d * (z • k) a b * conj (l c d)) =
      z * (∑ a, ∑ b, ∑ c, ∑ d,
        (gInv a c : ℂ) * gInv b d * k a b * conj (l c d)) := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro c hc
    apply Finset.sum_congr rfl
    intro d hd
    ring
  simp only [hermitianPhysicalPairing, hsum, complexMetricTrace_smul]
  ring

theorem hermitianPhysicalPairing_add_right (gInv : Tensor2) (k l m : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) :
    hermitianPhysicalPairing gInv k (l + m) =
      hermitianPhysicalPairing gInv k l + hermitianPhysicalPairing gInv k m := by
  rw [hermitianPhysicalPairing_conj_symm gInv k (l + m) hg,
    hermitianPhysicalPairing_add_left]
  simp only [map_add]
  rw [← hermitianPhysicalPairing_conj_symm gInv k l hg,
    ← hermitianPhysicalPairing_conj_symm gInv k m hg]

theorem hermitianPhysicalPairing_smul_right (gInv : Tensor2) (z : ℂ) (k l : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) :
    hermitianPhysicalPairing gInv k (z • l) = conj z * hermitianPhysicalPairing gInv k l := by
  rw [hermitianPhysicalPairing_conj_symm gInv k (z • l) hg,
    hermitianPhysicalPairing_smul_left]
  simp only [map_mul]
  rw [← hermitianPhysicalPairing_conj_symm gInv k l hg]

/-- The full Hermitian null formula for independently quantified complex
symmetric amplitudes in the same Ricci kernel. -/
theorem hermitianQuadraticSymbol_eq_physicalPairing_of_null_kernel
    (gInv : Tensor2) (ξ : Covector) (k l : ComplexTensor2)
    (hg : IsSymmetricTensor gInv) (hkSymm : IsSymmetricComplexTensor k)
    (hlSymm : IsSymmetricComplexTensor l) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) (b c : Index) :
    hermitianQuadraticSymbol gInv ξ k l b c =
      (ξ b : ℂ) * ξ c * hermitianPhysicalPairing gInv k l / 4 := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff gInv ξ k).mp hk
  obtain ⟨hlr, hli⟩ := (complexRicci_kernel_iff gInv ξ l).mp hl
  have hkrS := tensorRe_symmetric k hkSymm
  have hkiS := tensorIm_symmetric k hkSymm
  have hlrS := tensorRe_symmetric l hlSymm
  have hliS := tensorIm_symmetric l hlSymm
  apply Complex.ext
  · simp [hermitianQuadraticSymbol_re, Complex.mul_re, Complex.mul_im, hermitianPhysicalPairing_re]
    rw [mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ _ _ hg hkrS hlrS hξ hs hkr hlr,
      mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ _ _ hg hkiS hliS hξ hs hki hli]
    ring
  · simp [hermitianQuadraticSymbol_im, Complex.mul_re, Complex.mul_im, hermitianPhysicalPairing_im]
    rw [mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ _ _ hg hkiS hlrS hξ hs hki hlr,
      mixedQuadraticSymbol_eq_physicalPairing_of_null_kernel gInv ξ _ _ hg hkrS hliS hξ hs hkr hli]
    ring

end Burnett.RicciSymbol
