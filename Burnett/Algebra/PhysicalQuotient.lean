import Burnett.Algebra.NullNormalForm
import Burnett.Algebra.NullFrame

noncomputable section

namespace Burnett.RicciSymbol.PhysicalQuotient

open scoped ComplexConjugate
open TensorFrame

/-- Two physical coordinates, in one common frame chosen from the metric and
frequency alone, independently of the amplitude. -/
def coordinates (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (k : ComplexTensor2) : ℂ × ℂ :=
  NullNormalForm.screenCoordinates (NullFrame.normalizedFrame gInv base ξ hξ hs).components k

theorem coordinates_add (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) (k l : ComplexTensor2) :
    coordinates gInv base ξ hξ hs (k + l) =
      coordinates gInv base ξ hξ hs k + coordinates gInv base ξ hξ hs l :=
  NullNormalForm.screenCoordinates_add _ k l

theorem coordinates_smul (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) (z : ℂ) (k : ComplexTensor2) :
    coordinates gInv base ξ hξ hs (z • k) = z • coordinates gInv base ξ hξ hs k :=
  NullNormalForm.screenCoordinates_smul _ z k

/-- The two complex coordinates classify actual gauge classes in the original
null Ricci kernel, without assuming an already normalized frequency. -/
theorem gauge_iff_coordinates (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (k l : ComplexTensor2) (hkSymm : IsSymmetricComplexTensor k)
    (hlSymm : IsSymmetricComplexTensor l)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) :
    (∃ v : ComplexCovector, k = l + complexPureGauge ξ v) ↔
      coordinates gInv base ξ hξ hs k = coordinates gInv base ξ hξ hs l :=
  NullNormalForm.same_screenCoordinates_iff_gauge gInv
    (NullFrame.normalizedFrame gInv base ξ hξ hs) ξ
    (NullFrame.normalizedFrame_frequency gInv base ξ hξ hs) k l hkSymm hlSymm hk hl

/-- Every pair is realized by a genuine symmetric amplitude in the original
kernel. Together with gauge_iff_coordinates and linearity, this gives the
two-dimensional physical-class classification in both directions. -/
theorem all_coordinates_realized (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0) (u v : ℂ) :
    ∃ k : ComplexTensor2, IsSymmetricComplexTensor k ∧
      (∀ a b, complexRicciSymbol gInv ξ k a b = 0) ∧
      coordinates gInv base ξ hξ hs k = (u, v) :=
  NullNormalForm.screenCoordinates_surjective gInv
    (NullFrame.normalizedFrame gInv base ξ hξ hs) ξ
    (NullFrame.normalizedFrame_frequency gInv base ξ hξ hs) u v

theorem pairing_eq_coordinates (gInv : Tensor2) (base : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) (hs : symbolNorm gInv ξ = 0)
    (k l : ComplexTensor2) (hkSymm : IsSymmetricComplexTensor k)
    (hlSymm : IsSymmetricComplexTensor l)
    (hk : ∀ a b, complexRicciSymbol gInv ξ k a b = 0)
    (hl : ∀ a b, complexRicciSymbol gInv ξ l a b = 0) :
    hermitianPhysicalPairing gInv k l =
      2 * ((coordinates gInv base ξ hξ hs k).1 * conj (coordinates gInv base ξ hξ hs l).1 +
        (coordinates gInv base ξ hξ hs k).2 * conj (coordinates gInv base ξ hξ hs l).2) :=
  NullNormalForm.hermitianPhysicalPairing_eq_coordinates gInv
    (NullFrame.normalizedFrame gInv base ξ hξ hs) ξ
    (NullFrame.normalizedFrame_frequency gInv base ξ hξ hs) k l hkSymm hlSymm hk hl

end Burnett.RicciSymbol.PhysicalQuotient
