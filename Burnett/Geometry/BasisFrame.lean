import Burnett.Geometry.FiberMetric
import Burnett.Algebra.LorentzPhysical

/-!
# From a metric-orthonormal fiber basis to the existing F06 frame

The coordinate and orthonormal bases below are genuine bases of the same
vector space, and the normal-form assumption concerns the covariant bilinear
form itself. The inverse-metric normal form and bijectivity required by F06
are proved. Existence or smooth choice of the orthonormal basis is separate.
-/

noncomputable section

namespace Burnett.Geometry.BasisFrame

open scoped BigOperators
open Module
open Burnett.RicciSymbol
open FiberMetric

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Columns are the actual frame vectors expressed in the coordinate basis. -/
def components (b c : Basis Index ℝ V) : Tensor2 := fun i a => vector b (c a) i

theorem covector_components (b c : Basis Index ℝ V) (ξ : Module.Dual ℝ V) :
    TensorFrame.covector (components b c) (covector b ξ) = covector c ξ := by
  funext a
  exact (covector_eval b ξ (c a)).symm

/-- The old double finite sum is the actual change of components of any
covariant bilinear tensor on the fiber. -/
theorem tensor_components (b c : Basis Index ℝ V) (k : LinearMap.BilinForm ℝ V) :
    TensorFrame.tensor (components b c) (covariant k b) = covariant k c := by
  funext a d
  have h := congrArg₂ (fun v w : V => k v w) (b.sum_repr (c a)) (b.sum_repr (c d))
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum] at h
  rw [Finset.sum_comm] at h
  simpa only [TensorFrame.tensor, components, covariant, vector, Basis.equivFun_apply,
    mul_assoc, mul_left_comm, mul_comm] using h

theorem covector_bijective (b c : Basis Index ℝ V) :
    Function.Bijective (TensorFrame.covector (components b c)) := by
  have h (d : Basis Index ℝ V) (ξ : Module.Dual ℝ V) :
      d.dualBasis.equivFun ξ = covector d ξ := by
    funext i
    exact Basis.dualBasis_equivFun d ξ i
  have heq : TensorFrame.covector (components b c) =
      c.dualBasis.equivFun ∘ b.dualBasis.equivFun.symm := by
    funext ξ
    obtain ⟨ξ, rfl⟩ := b.dualBasis.equivFun.surjective ξ
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
    rw [h, covector_components]
    exact (h c ξ).symm
  rw [heq]
  exact c.dualBasis.equivFun.bijective.comp b.dualBasis.equivFun.symm.bijective

theorem signature_sq (i : Index) : TensorFrame.signature i * TensorFrame.signature i = 1 := by
  unfold TensorFrame.signature
  split_ifs <;> norm_num

/-- A Lorentz-orthonormal basis allows extraction of coordinates from the
actual metric pairing. -/
theorem coordinate_eq_signature_pairing (g : LinearMap.BilinForm ℝ V)
    (c : Basis Index ℝ V)
    (hc : ∀ a d, g (c a) (c d) = TensorFrame.standardInverse a d)
    (v : V) (a : Index) :
    vector c v a = TensorFrame.signature a * g v (c a) := by
  have h := congrArg (fun v : V => g v (c a)) (c.sum_repr v)
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    smul_eq_mul, hc, TensorFrame.standardInverse] at h
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h
  rw [← h]
  simp only [vector, Basis.equivFun_apply]
  rw [← mul_assoc, mul_comm (TensorFrame.signature a), mul_assoc, signature_sq, mul_one]

/-- Nondegeneracy follows from the covariant orthonormal-basis equation. -/
theorem nondegenerate_of_orthonormal (g : LinearMap.BilinForm ℝ V)
    (c : Basis Index ℝ V)
    (hc : ∀ a d, g (c a) (c d) = TensorFrame.standardInverse a d) : g.Nondegenerate := by
  intro v hv
  apply c.equivFun.injective
  ext a
  have ha := coordinate_eq_signature_pairing g c hc v a
  simpa only [vector, hv, mul_zero, map_zero, Pi.zero_apply] using ha

/-- The inverse-metric identity needed by the existing LorentzFrame is a
consequence of the genuine covariant metric's orthonormal basis. -/
theorem inverseMetric_components (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (b c : Basis Index ℝ V)
    (hc : ∀ a d, g (c a) (c d) = TensorFrame.standardInverse a d) :
    TensorFrame.inverseMetric (components b c) = contravariant g hg b := by
  funext i j
  have h := congrArg (g (g.dualBasis hg b i)) (c.sum_repr (g.dualBasis hg b j))
  simp only [map_sum, map_smul, smul_eq_mul] at h
  have hc' (a : Index) : c.repr (g.dualBasis hg b j) a =
      TensorFrame.signature a * g (g.dualBasis hg b j) (c a) := by
    simpa only [vector, Basis.equivFun_apply] using
      coordinate_eq_signature_pairing g c hc (g.dualBasis hg b j) a
  simp_rw [hc', dualBasis_pairing] at h
  rw [contravariant_eq_coordinate]
  simpa only [TensorFrame.inverseMetric, components, contravariant, vector,
    Basis.equivFun_apply, mul_assoc, mul_comm, mul_left_comm] using h

/-- A genuine metric fiber with a supplied Lorentz-orthonormal basis provides
the old F06 certificate in any coordinate basis. -/
def lorentzFrame (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (b c : Basis Index ℝ V)
    (hc : ∀ a d, g (c a) (c d) = TensorFrame.standardInverse a d) :
    TensorFrame.LorentzFrame (contravariant g hg b) where
  components := components b c
  isBasis := covector_bijective b c
  inverseMetric_eq := inverseMetric_components g hg b c hc

/-- F06 positivity can now be consumed using a covariant bilinear metric and
its actual orthonormal basis; no inverse-metric normal form is assumed. -/
theorem physicalPairing_self_nonneg (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (b c : Basis Index ℝ V)
    (hc : ∀ a d, g (c a) (c d) = TensorFrame.standardInverse a d)
    (ξ : Covector) (k : Tensor2) (hkSymm : IsSymmetricTensor k) (hξ : ξ ≠ 0)
    (hs : symbolNorm (contravariant g hg b) ξ = 0)
    (hk : ∀ a d, ricciSymbol (contravariant g hg b) ξ k a d = 0) :
    0 ≤ physicalPairing (contravariant g hg b) k k :=
  LorentzPhysical.physicalPairing_self_nonneg _ (lorentzFrame g hg b c hc)
    ξ k hkSymm hξ hs hk

/-- An explicit bilinear metric with one negative and three positive squares,
defined on an actual vector space using any genuine four-element basis. -/
def modelMetric (c : Basis Index ℝ V) : LinearMap.BilinForm ℝ V :=
  ∑ a, TensorFrame.signature a • LinearMap.BilinForm.linMulLin (c.coord a) (c.coord a)

theorem modelMetric_apply (c : Basis Index ℝ V) (v w : V) :
    modelMetric c v w = ∑ a, TensorFrame.signature a * vector c v a * vector c w a := by
  simp [modelMetric, vector, LinearMap.BilinForm.linMulLin_apply, Basis.coord_apply,
    Basis.equivFun_apply, mul_assoc]

theorem modelMetric_orthonormal (c : Basis Index ℝ V) (a d : Index) :
    modelMetric c (c a) (c d) = TensorFrame.standardInverse a d := by
  by_cases had : a = d
  · subst d
    simp [modelMetric_apply, vector, TensorFrame.standardInverse, Basis.equivFun_self, mul_ite]
  · simp [modelMetric_apply, vector, TensorFrame.standardInverse, Basis.equivFun_self,
      mul_ite, had]

theorem modelMetric_nondegenerate (c : Basis Index ℝ V) :
    (modelMetric c).Nondegenerate :=
  nondegenerate_of_orthonormal _ c (modelMetric_orthonormal c)

/-- A concrete nonempty instance on the standard real four-dimensional
coordinate vector space, now derived from a bilinear metric. -/
def standardFiberFrame : TensorFrame.LorentzFrame
    (contravariant (modelMetric (Pi.basisFun ℝ Index))
      (modelMetric_nondegenerate (Pi.basisFun ℝ Index)) (Pi.basisFun ℝ Index)) :=
  lorentzFrame _ (modelMetric_nondegenerate _) _ _ (modelMetric_orthonormal _)

end Burnett.Geometry.BasisFrame
