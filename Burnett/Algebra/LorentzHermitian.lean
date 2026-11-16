import Burnett.Algebra.LorentzPhysical

noncomputable section

namespace Burnett.RicciSymbol.LorentzHermitian

open TensorFrame

/-- The physical Hermitian form has nonnegative real diagonal on the null
Ricci kernel for every inverse metric with an explicit Lorentz frame. -/
theorem physicalPairing_self_re_nonneg (gInv : Tensor2) (frame : LorentzFrame gInv)
    (ξ : Covector) (k : ComplexTensor2) (hkSymm : IsSymmetricComplexTensor k)
    (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0) :
    0 ≤ (hermitianPhysicalPairing gInv k k).re := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff gInv ξ k).mp hk
  rw [hermitianPhysicalPairing_diag_re]
  exact add_nonneg
    (LorentzPhysical.physicalPairing_self_nonneg gInv frame ξ _
      (tensorRe_symmetric k hkSymm) hξ hs hkr)
    (LorentzPhysical.physicalPairing_self_nonneg gInv frame ξ _
      (tensorIm_symmetric k hkSymm) hξ hs hki)

/-- Reality follows from the original Hermitian contraction, independently
of the Ricci-kernel condition. -/
theorem physicalPairing_self_im_eq_zero (gInv : Tensor2) (frame : LorentzFrame gInv)
    (k : ComplexTensor2) : (hermitianPhysicalPairing gInv k k).im = 0 :=
  hermitianPhysicalPairing_diag_im gInv k (LorentzPhysical.metric_symmetric gInv frame)

/-- The radical of the null-kernel Hermitian form is exactly the actual
complex pure-gauge subspace. The frame supplies no positivity assumption. -/
theorem physicalPairing_self_eq_zero_iff_pureGauge
    (gInv : Tensor2) (frame : LorentzFrame gInv) (ξ : Covector) (k : ComplexTensor2)
    (hkSymm : IsSymmetricComplexTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0) :
    hermitianPhysicalPairing gInv k k = 0 ↔
      ∃ v : ComplexCovector, k = complexPureGauge ξ v := by
  obtain ⟨hkr, hki⟩ := (complexRicci_kernel_iff gInv ξ k).mp hk
  have hkrS := tensorRe_symmetric k hkSymm
  have hkiS := tensorIm_symmetric k hkSymm
  constructor
  · intro hz
    have hzR : physicalPairing gInv (tensorRe k) (tensorRe k) +
        physicalPairing gInv (tensorIm k) (tensorIm k) = 0 := by
      simpa only [hermitianPhysicalPairing_diag_re, Complex.zero_re] using congrArg Complex.re hz
    have hrr := LorentzPhysical.physicalPairing_self_nonneg gInv frame ξ _ hkrS hξ hs hkr
    have hii := LorentzPhysical.physicalPairing_self_nonneg gInv frame ξ _ hkiS hξ hs hki
    have hzkr : physicalPairing gInv (tensorRe k) (tensorRe k) = 0 := by linarith
    have hzki : physicalPairing gInv (tensorIm k) (tensorIm k) = 0 := by linarith
    obtain ⟨vr, hvr⟩ :=
      (LorentzPhysical.physicalPairing_self_eq_zero_iff_pureGauge gInv frame ξ _ hkrS hξ hs hkr).mp hzkr
    obtain ⟨vi, hvi⟩ :=
      (LorentzPhysical.physicalPairing_self_eq_zero_iff_pureGauge gInv frame ξ _ hkiS hξ hs hki).mp hzki
    refine ⟨fun a => (vr a : ℂ) + (vi a : ℂ) * Complex.I, ?_⟩
    funext a b
    apply Complex.ext
    · simpa [tensorRe, complexPureGauge, pureGauge, Complex.mul_re, Complex.mul_im] using
        congrFun (congrFun hvr a) b
    · simpa [tensorIm, complexPureGauge, pureGauge, Complex.mul_re, Complex.mul_im] using
        congrFun (congrFun hvi a) b
  · rintro ⟨v, hv⟩
    calc
      hermitianPhysicalPairing gInv k k =
          hermitianPhysicalPairing gInv k (complexPureGauge ξ v) := by rw [← hv]
      _ = 0 := hermitianPhysicalPairing_pureGauge_eq_zero_of_null_kernel
        gInv ξ k v (LorentzPhysical.metric_symmetric gInv frame) hkSymm hξ hs hk

end Burnett.RicciSymbol.LorentzHermitian
