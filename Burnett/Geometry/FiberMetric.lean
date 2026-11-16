import Burnett.Algebra.TensorFrame
import Mathlib.LinearAlgebra.BilinearForm.Properties

/-!
# A genuine metric fiber and its coordinate inverse

The input is a nondegenerate bilinear form on a real vector space and an
actual four-element basis. The inverse metric is constructed from the
metric-dual basis; no matrix-inverse identity or Ricci conclusion is an input.
This is a pointwise bridge, with no manifold, regularity, signature, or
global-frame assertion.
-/

noncomputable section

namespace Burnett.Geometry.FiberMetric

open scoped BigOperators
open Module
open Burnett.RicciSymbol

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Components of a covariant metric in a genuine basis. -/
def covariant (g : LinearMap.BilinForm ℝ V) (b : Basis Index ℝ V) : Tensor2 :=
  fun i j => g (b i) (b j)

/-- Components of a genuine linear covector. -/
def covector (b : Basis Index ℝ V) (ξ : Module.Dual ℝ V) : Covector :=
  fun i => ξ (b i)

/-- Coordinates of a genuine vector. -/
def vector (b : Basis Index ℝ V) (v : V) : Index → ℝ := b.equivFun v

/-- The inverse metric is evaluated on the metric-dual basis. -/
def contravariant (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (b : Basis Index ℝ V) : Tensor2 :=
  fun i j => g (g.dualBasis hg b i) (g.dualBasis hg b j)

/-- The actual inverse of the metric's lowering map. Finite dimensionality
comes from the supplied basis. -/
def sharp (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (b : Basis Index ℝ V) : Module.Dual ℝ V ≃ₗ[ℝ] V := by
  letI := FiniteDimensional.of_fintype_basis b
  exact (g.toDual hg).symm

theorem covector_eval (b : Basis Index ℝ V) (ξ : Module.Dual ℝ V) (v : V) :
    ξ v = ∑ i, vector b v i * covector b ξ i := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  simp [vector, covector, Basis.equivFun_apply]

theorem dualBasis_pairing (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (b : Basis Index ℝ V) (i : Index) (v : V) :
    g (g.dualBasis hg b i) v = vector b v i := by
  conv_lhs => rw [← b.sum_repr v]
  rw [map_sum]
  simp [vector, Basis.equivFun_apply, LinearMap.BilinForm.apply_dualBasis_left]

theorem contravariant_eq_coordinate (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (b : Basis Index ℝ V) (i j : Index) :
    contravariant g hg b i j = vector b (g.dualBasis hg b j) i :=
  dualBasis_pairing g hg b i _

theorem covariant_symmetric (g : LinearMap.BilinForm ℝ V)
    (hs : g.IsSymm) (b : Basis Index ℝ V) : IsSymmetricTensor (covariant g b) :=
  fun i j => hs.eq (b i) (b j)

theorem contravariant_symmetric (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) :
    IsSymmetricTensor (contravariant g hg b) :=
  fun _ _ => hs.eq _ _

/-- Both indices range over all four coordinates, as in the existing F06
tensor algebra. This identity is derived from nondegeneracy, not supplied. -/
theorem covariant_mul_contravariant (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) (i k : Index) :
    (∑ j, covariant g b i j * contravariant g hg b j k) =
      if i = k then 1 else 0 := by
  simp_rw [contravariant_eq_coordinate, covariant, vector, Basis.equivFun_apply]
  have h := congrArg (g (b i)) (b.sum_repr (g.dualBasis hg b k))
  simp only [map_sum, map_smul, smul_eq_mul] at h
  simpa only [mul_comm, LinearMap.BilinForm.apply_dualBasis_right g hg hs] using h

theorem contravariant_mul_covariant (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (hs : g.IsSymm) (b : Basis Index ℝ V) (i k : Index) :
    (∑ j, contravariant g hg b i j * covariant g b j k) =
      if i = k then 1 else 0 := by
  calc
    _ = ∑ j, covariant g b k j * contravariant g hg b j i := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [contravariant_symmetric g hg hs b i j, covariant_symmetric g hs b j k]
      exact mul_comm _ _
    _ = _ := by simpa only [eq_comm] using covariant_mul_contravariant g hg hs b k i

@[simp] theorem sharp_lower (g : LinearMap.BilinForm ℝ V) (hg : g.Nondegenerate)
    (b : Basis Index ℝ V) (ξ : Module.Dual ℝ V) (v : V) :
    g (sharp g hg b ξ) v = ξ v := by
  letI := FiniteDimensional.of_fintype_basis b
  exact LinearMap.BilinForm.apply_toDual_symm_apply ξ v

/-- The old finite-sum raising operation is the coordinates of the actual
inverse lowering map on the vector-space dual. -/
theorem raiseCovector_eq_sharp (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (b : Basis Index ℝ V) (ξ : Module.Dual ℝ V) :
    raiseCovector (contravariant g hg b) (covector b ξ) = vector b (sharp g hg b ξ) := by
  funext i
  have h := congrArg (fun v : V => vector b v i)
    ((g.dualBasis hg b).sum_repr (sharp g hg b ξ))
  simp only [LinearMap.BilinForm.dualBasis_repr_apply, sharp_lower] at h
  simp only [vector, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Basis.equivFun_apply] at h
  simpa only [raiseCovector, covector, contravariant_eq_coordinate, vector,
    Basis.equivFun_apply, mul_comm] using h

/-- The characteristic quadratic symbol is the intrinsic dual metric norm. -/
theorem symbolNorm_eq_eval_sharp (g : LinearMap.BilinForm ℝ V)
    (hg : g.Nondegenerate) (b : Basis Index ℝ V) (ξ : Module.Dual ℝ V) :
    symbolNorm (contravariant g hg b) (covector b ξ) = ξ (sharp g hg b ξ) := by
  rw [covector_eval b ξ (sharp g hg b ξ)]
  simp only [symbolNorm, ← raiseCovector_eq_sharp]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [raiseCovector, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end Burnett.Geometry.FiberMetric
