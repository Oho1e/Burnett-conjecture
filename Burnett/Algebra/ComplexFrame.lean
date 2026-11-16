import Burnett.Algebra.MinkowskiNull
import Burnett.Algebra.TensorFrame

noncomputable section

namespace Burnett.RicciSymbol.ComplexFrame

open scoped BigOperators ComplexConjugate

private theorem cf_re_sum (f : Index → ℂ) : (∑ a, f a).re = ∑ a, (f a).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

private theorem cf_im_sum (f : Index → ℂ) : (∑ a, f a).im = ∑ a, (f a).im :=
  map_sum Complex.imAddGroupHom f Finset.univ

/-- The actual pullback of a complex covector under a real coordinate frame. -/
def complexCovector (e : Tensor2) (v : ComplexCovector) : ComplexCovector := fun a =>
  ∑ i, (e i a : ℂ) * v i

/-- The actual covariant two-tensor transformation, with both real frame
coefficients and all ordered indices retained. -/
def complexTensor (e : Tensor2) (k : ComplexTensor2) : ComplexTensor2 := fun a b =>
  ∑ i, ∑ j, (e i a : ℂ) * e j b * k i j

@[simp] theorem complexCovector_re (e : Tensor2) (v : ComplexCovector) :
    (fun a => (complexCovector e v a).re) = TensorFrame.covector e (fun i => (v i).re) := by
  funext a
  simp [complexCovector, TensorFrame.covector, cf_re_sum, Complex.mul_re]

@[simp] theorem complexCovector_im (e : Tensor2) (v : ComplexCovector) :
    (fun a => (complexCovector e v a).im) = TensorFrame.covector e (fun i => (v i).im) := by
  funext a
  simp [complexCovector, TensorFrame.covector, cf_im_sum, Complex.mul_im]

@[simp] theorem complexTensor_re (e : Tensor2) (k : ComplexTensor2) :
    tensorRe (complexTensor e k) = TensorFrame.tensor e (tensorRe k) := by
  funext a b
  simp [complexTensor, TensorFrame.tensor, tensorRe, cf_re_sum, Complex.mul_re, Complex.mul_im]

@[simp] theorem complexTensor_im (e : Tensor2) (k : ComplexTensor2) :
    tensorIm (complexTensor e k) = TensorFrame.tensor e (tensorIm k) := by
  funext a b
  simp [complexTensor, TensorFrame.tensor, tensorIm, cf_im_sum, Complex.mul_re, Complex.mul_im]

theorem complexTensor_symmetric (e : Tensor2) (k : ComplexTensor2)
    (hk : IsSymmetricComplexTensor k) : IsSymmetricComplexTensor (complexTensor e k) := by
  intro a b
  apply Complex.ext
  · simpa only [← complexTensor_re e k] using
      TensorFrame.tensor_symmetric e (tensorRe k) (tensorRe_symmetric k hk) a b
  · simpa only [← complexTensor_im e k] using
      TensorFrame.tensor_symmetric e (tensorIm k) (tensorIm_symmetric k hk) a b

/-- A change to an actual Lorentz frame preserves the full complex physical
contraction, not merely its diagonal or its real part. -/
theorem hermitianPhysicalPairing_transform (e : Tensor2) (k l : ComplexTensor2) :
    hermitianPhysicalPairing (TensorFrame.inverseMetric e) k l =
      hermitianPhysicalPairing TensorFrame.standardInverse (complexTensor e k) (complexTensor e l) := by
  apply Complex.ext
  · simp only [hermitianPhysicalPairing_re, complexTensor_re, complexTensor_im,
      TensorFrame.physicalPairing_transform]
  · simp only [hermitianPhysicalPairing_im, complexTensor_im, complexTensor_re,
      TensorFrame.physicalPairing_transform]

/-- Null-kernel covariance follows from the actual real covariance theorem for
both real and imaginary amplitudes. No positivity or quotient statement is assumed. -/
theorem complex_null_kernel_transform (e : Tensor2) (ξ : Covector) (k : ComplexTensor2)
    (hξ : ξ ≠ 0) (hs : symbolNorm (TensorFrame.inverseMetric e) ξ = 0)
    (hk : ∀ a b, complexRicciSymbol (TensorFrame.inverseMetric e) ξ k a b = 0) :
    ∀ a b, complexRicciSymbol TensorFrame.standardInverse (TensorFrame.covector e ξ)
      (complexTensor e k) a b = 0 := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff (TensorFrame.inverseMetric e) ξ k).mp hk
  apply (complexRicci_kernel_iff TensorFrame.standardInverse (TensorFrame.covector e ξ) (complexTensor e k)).mpr
  constructor
  · simpa only [complexTensor_re] using TensorFrame.null_kernel_transform e (tensorRe k) ξ hξ hs hkr
  · simpa only [complexTensor_im] using TensorFrame.null_kernel_transform e (tensorIm k) ξ hξ hs hki

/-- Gauge addition is natural for the actual two-tensor and covector maps. -/
theorem complexTensor_pureGauge (e : Tensor2) (ξ : Covector) (v : ComplexCovector) :
    complexTensor e (complexPureGauge ξ v) =
      complexPureGauge (TensorFrame.covector e ξ) (complexCovector e v) := by
  funext a b
  apply Complex.ext
  · change tensorRe (complexTensor e (complexPureGauge ξ v)) a b =
      tensorRe (complexPureGauge (TensorFrame.covector e ξ) (complexCovector e v)) a b
    simp only [complexTensor_re, tensorRe_complexPureGauge, TensorFrame.tensor_pureGauge,
      complexCovector_re]
  · change tensorIm (complexTensor e (complexPureGauge ξ v)) a b =
      tensorIm (complexPureGauge (TensorFrame.covector e ξ) (complexCovector e v)) a b
    simp only [complexTensor_im, tensorIm_complexPureGauge, TensorFrame.tensor_pureGauge,
      complexCovector_im]

theorem complexTensor_injective (e : Tensor2) (he : Function.Injective (TensorFrame.covector e)) :
    Function.Injective (complexTensor e) := by
  intro k l h
  have hr := congrArg tensorRe h
  have hi := congrArg tensorIm h
  rw [complexTensor_re, complexTensor_re] at hr
  rw [complexTensor_im, complexTensor_im] at hi
  have hkr := TensorFrame.tensor_injective e he hr
  have hki := TensorFrame.tensor_injective e he hi
  funext a b
  apply Complex.ext
  · exact congrFun (congrFun hkr a) b
  · exact congrFun (congrFun hki a) b

theorem complexCovector_surjective (e : Tensor2) (he : Function.Surjective (TensorFrame.covector e)) :
    Function.Surjective (complexCovector e) := by
  intro v
  obtain ⟨vr, hvr⟩ := he (fun a => (v a).re)
  obtain ⟨vi, hvi⟩ := he (fun a => (v a).im)
  refine ⟨fun a => (vr a : ℂ) + (vi a : ℂ) * Complex.I, ?_⟩
  funext a
  apply Complex.ext
  · simpa [complexCovector, TensorFrame.covector, cf_re_sum, Complex.mul_re, Complex.mul_im] using congrFun hvr a
  · simpa [complexCovector, TensorFrame.covector, cf_im_sum, Complex.mul_re, Complex.mul_im] using congrFun hvi a

/-- Positivity in every nonzero Minkowski-null direction, obtained from the
two real amplitudes and the already proved actual physical pairing. -/
theorem minkowski_hermitianPhysicalPairing_self_re_nonneg
    (ξ : Covector) (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm NullScreen.minkowskiInverse ξ = 0)
    (hk : ∀ a b, complexRicciSymbol NullScreen.minkowskiInverse ξ k a b = 0) :
    0 ≤ (hermitianPhysicalPairing NullScreen.minkowskiInverse k k).re := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff NullScreen.minkowskiInverse ξ k).mp hk
  rw [hermitianPhysicalPairing_diag_re]
  exact add_nonneg
    (MinkowskiNull.physicalPairing_self_nonneg ξ _ (tensorRe_symmetric k hkSymm) hξ hs hkr)
    (MinkowskiNull.physicalPairing_self_nonneg ξ _ (tensorIm_symmetric k hkSymm) hξ hs hki)

theorem minkowski_hermitianPhysicalPairing_self_im_eq_zero (k : ComplexTensor2) :
    (hermitianPhysicalPairing NullScreen.minkowskiInverse k k).im = 0 :=
  hermitianPhysicalPairing_diag_im _ k NullScreen.minkowskiInverse_symmetric

/-- The radical is exactly actual complex pure gauge, for arbitrary nonzero
null frequency rather than only the standard (-1,1,0,0) representative. -/
theorem minkowski_hermitianPhysicalPairing_self_eq_zero_iff_pureGauge
    (ξ : Covector) (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm NullScreen.minkowskiInverse ξ = 0)
    (hk : ∀ a b, complexRicciSymbol NullScreen.minkowskiInverse ξ k a b = 0) :
    hermitianPhysicalPairing NullScreen.minkowskiInverse k k = 0 ↔
      ∃ v : ComplexCovector, k = complexPureGauge ξ v := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff NullScreen.minkowskiInverse ξ k).mp hk
  have hkrS := tensorRe_symmetric k hkSymm
  have hkiS := tensorIm_symmetric k hkSymm
  constructor
  · intro hz
    have hzR : physicalPairing NullScreen.minkowskiInverse (tensorRe k) (tensorRe k) +
        physicalPairing NullScreen.minkowskiInverse (tensorIm k) (tensorIm k) = 0 := by
      simpa only [hermitianPhysicalPairing_diag_re, Complex.zero_re] using congrArg Complex.re hz
    have hrr := MinkowskiNull.physicalPairing_self_nonneg ξ _ hkrS hξ hs hkr
    have hii := MinkowskiNull.physicalPairing_self_nonneg ξ _ hkiS hξ hs hki
    have hzkr : physicalPairing NullScreen.minkowskiInverse (tensorRe k) (tensorRe k) = 0 := by linarith
    have hzki : physicalPairing NullScreen.minkowskiInverse (tensorIm k) (tensorIm k) = 0 := by linarith
    obtain ⟨vr, hvr⟩ := (MinkowskiNull.physicalPairing_self_eq_zero_iff_pureGauge ξ _ hkrS hξ hs hkr).mp hzkr
    obtain ⟨vi, hvi⟩ := (MinkowskiNull.physicalPairing_self_eq_zero_iff_pureGauge ξ _ hkiS hξ hs hki).mp hzki
    refine ⟨fun a => (vr a : ℂ) + (vi a : ℂ) * Complex.I, ?_⟩
    funext a b
    apply Complex.ext
    · simpa [tensorRe, complexPureGauge, pureGauge, Complex.mul_re, Complex.mul_im] using
        congrFun (congrFun hvr a) b
    · simpa [tensorIm, complexPureGauge, pureGauge, Complex.mul_re, Complex.mul_im] using
        congrFun (congrFun hvi a) b
  · rintro ⟨v, hv⟩
    calc
      hermitianPhysicalPairing NullScreen.minkowskiInverse k k =
          hermitianPhysicalPairing NullScreen.minkowskiInverse k (complexPureGauge ξ v) := by rw [← hv]
      _ = 0 := hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel
        NullScreen.minkowskiInverse ξ k v NullScreen.minkowskiInverse_symmetric hkSymm hξ hs hk

end Burnett.RicciSymbol.ComplexFrame
