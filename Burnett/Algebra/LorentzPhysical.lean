import Burnett.Algebra.TensorFrame
import Burnett.Algebra.MinkowskiNull

/-!
# The physical form under an actual Lorentz-frame certificate

The supplied frame consists only of a bijective coordinate change and the
inverse metric's Lorentz normal form. Positivity and the physical null space
are derived here. Existence of this certificate from an independent geometric
definition of a Lorentz metric remains a separate interface.
-/

noncomputable section

namespace Burnett.RicciSymbol.LorentzPhysical

open TensorFrame

theorem standardInverse_eq_minkowski : standardInverse = NullScreen.minkowskiInverse := rfl

theorem metric_symmetric (gInv : Tensor2) (frame : LorentzFrame gInv) :
    IsSymmetricTensor gInv := by
  rw [← frame.inverseMetric_eq]
  exact inverseMetric_symmetric frame.components

theorem transformed_covector_ne_zero (gInv : Tensor2) (frame : LorentzFrame gInv)
    (ξ : Covector) (hξ : ξ ≠ 0) : covector frame.components ξ ≠ 0 :=
  covector_ne_zero frame.components frame.isBasis.1 ξ hξ

theorem transformed_symbolNorm (gInv : Tensor2) (frame : LorentzFrame gInv)
    (ξ : Covector) :
    symbolNorm NullScreen.minkowskiInverse (covector frame.components ξ) =
      symbolNorm gInv ξ := by
  rw [← standardInverse_eq_minkowski, ← symbolNorm_transform, frame.inverseMetric_eq]

theorem transformed_null_kernel (gInv : Tensor2) (frame : LorentzFrame gInv)
    (ξ : Covector) (k : Tensor2) (hξ : ξ ≠ 0)
    (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    ∀ a b, ricciSymbol NullScreen.minkowskiInverse
      (covector frame.components ξ) (tensor frame.components k) a b = 0 := by
  rw [← standardInverse_eq_minkowski]
  apply null_kernel_transform frame.components k ξ hξ
  · simpa only [frame.inverseMetric_eq] using hs
  · simpa only [frame.inverseMetric_eq] using hk

theorem physicalPairing_eq_transformed (gInv : Tensor2) (frame : LorentzFrame gInv)
    (k l : Tensor2) :
    physicalPairing gInv k l = physicalPairing NullScreen.minkowskiInverse
      (tensor frame.components k) (tensor frame.components l) := by
  calc
    physicalPairing gInv k l = physicalPairing (inverseMetric frame.components) k l :=
      congrArg (fun g => physicalPairing g k l) frame.inverseMetric_eq.symm
    _ = _ := by
      simpa only [standardInverse_eq_minkowski] using
        physicalPairing_transform frame.components k l

/-- Nonnegativity on the entire real symmetric null kernel in every frame
described by the certificate; no positive-form hypothesis is supplied. -/
theorem physicalPairing_self_nonneg (gInv : Tensor2) (frame : LorentzFrame gInv)
    (ξ : Covector) (k : Tensor2) (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    0 ≤ physicalPairing gInv k k := by
  rw [physicalPairing_eq_transformed gInv frame k k]
  exact MinkowskiNull.physicalPairing_self_nonneg (covector frame.components ξ)
    (tensor frame.components k) (tensor_symmetric frame.components k hkSymm)
    (transformed_covector_ne_zero gInv frame ξ hξ)
    (by rw [transformed_symbolNorm gInv frame ξ, hs])
    (transformed_null_kernel gInv frame ξ k hξ hs hk)

/-- A zero-norm tensor is an actual pure gauge tensor in the original
coordinates, rather than merely having a vanishing transformed screen. -/
theorem physicalPairing_self_eq_zero_iff_pureGauge
    (gInv : Tensor2) (frame : LorentzFrame gInv)
    (ξ : Covector) (k : Tensor2) (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm gInv ξ = 0)
    (hk : ∀ a b, ricciSymbol gInv ξ k a b = 0) :
    physicalPairing gInv k k = 0 ↔ ∃ v : Covector, k = pureGauge ξ v := by
  constructor
  · intro hz
    rw [physicalPairing_eq_transformed gInv frame k k] at hz
    obtain ⟨v', hkv'⟩ := (MinkowskiNull.physicalPairing_self_eq_zero_iff_pureGauge
      (covector frame.components ξ) (tensor frame.components k)
      (tensor_symmetric frame.components k hkSymm)
      (transformed_covector_ne_zero gInv frame ξ hξ)
      (by rw [transformed_symbolNorm gInv frame ξ, hs])
      (transformed_null_kernel gInv frame ξ k hξ hs hk)).mp hz
    obtain ⟨v, hv⟩ := frame.isBasis.2 v'
    refine ⟨v, tensor_injective frame.components frame.isBasis.1 ?_⟩
    rw [tensor_pureGauge, hv]
    exact hkv'
  · rintro ⟨v, hv⟩
    calc
      physicalPairing gInv k k = physicalPairing gInv k (pureGauge ξ v) := by rw [← hv]
      _ = 0 := physicalPairing_pureGauge_eq_zero_of_null_kernel gInv ξ k v
        (metric_symmetric gInv frame) hkSymm hξ hs hk

/-- Identity components give a concrete nonempty instance of the frame data. -/
def identityComponents : Tensor2 := fun a b => if a = b then 1 else 0

theorem covector_identity (ξ : Covector) : covector identityComponents ξ = ξ := by
  funext a
  simp [covector, identityComponents, ite_mul]

theorem inverseMetric_identity : inverseMetric identityComponents = standardInverse := by
  funext a b
  by_cases hab : a = b
  · subst b
    simp [inverseMetric, identityComponents, standardInverse, mul_ite]
  · simp [inverseMetric, identityComponents, standardInverse, mul_ite, hab]

def standardFrame : LorentzFrame NullScreen.minkowskiInverse where
  components := identityComponents
  isBasis := by
    constructor
    · intro ξ ζ h
      simpa only [covector_identity] using h
    · intro ξ
      exact ⟨ξ, covector_identity ξ⟩
  inverseMetric_eq := by rw [inverseMetric_identity, standardInverse_eq_minkowski]

end Burnett.RicciSymbol.LorentzPhysical
