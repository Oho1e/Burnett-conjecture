import Burnett.Geometry.ConnectionDifference
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Metric Set Burnett.Geometry.ConnectionDifference
open scoped ContDiff

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The literal coefficient difference in the rescaled spatial variable. -/
def rescaledSpatialDifference (A : CoordinateSpace → F) (c : CoordinateSpace) (ℓ : ℝ)
    (y : CoordinateSpace) : F := A (c + ℓ • y) - A c

theorem affine_rescaling_mem_closedBall (c y : CoordinateSpace) (S ℓ : ℝ)
    (hℓ : 0 ≤ ℓ) (hy : y ∈ closedBall (0 : CoordinateSpace) S) :
    c + ℓ • y ∈ closedBall c (S * ℓ) := by
  have hyNorm : ‖y‖ ≤ S := by simpa only [mem_closedBall, dist_zero_right] using hy
  rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hℓ, mul_comm S ℓ]
  exact mul_le_mul_of_nonneg_left hyNorm hℓ

/-- The zeroth derivative gains one scale factor by the mean-value theorem
on the actual physical closed ball. -/
theorem rescaled_spatial_difference_zero_bound (A : CoordinateSpace → F) (hA : ContDiff ℝ ∞ A)
    (c y : CoordinateSpace) (S ℓ M : ℝ) (hS : 0 ≤ S) (hℓ : 0 ≤ ℓ) (hM : 0 ≤ M)
    (hy : y ∈ closedBall (0 : CoordinateSpace) S)
    (hGradient : ∀ x ∈ closedBall c (S * ℓ), ‖fderiv ℝ A x‖ ≤ M) :
    ‖rescaledSpatialDifference A c ℓ y‖ ≤ M * (S * ℓ) := by
  have hx := affine_rescaling_mem_closedBall c y S ℓ hℓ hy
  have bound := (convex_closedBall c (S * ℓ)).norm_image_sub_le_of_norm_fderiv_le
    (fun x _ => (hA.differentiable (by simp)) x) hGradient
    (mem_closedBall_self (mul_nonneg hS hℓ)) hx
  exact bound.trans (mul_le_mul_of_nonneg_left (by simpa only [mem_closedBall, dist_eq_norm] using hx) hM)

/-- Each positive Fréchet derivative has the exact affine dilation factor.
The constant term in the difference contributes zero. -/
theorem rescaled_spatial_difference_succ_jet (A : CoordinateSpace → F) (hA : ContDiff ℝ ∞ A)
    (c y : CoordinateSpace) (ℓ : ℝ) (n : ℕ) :
    iteratedFDeriv ℝ (n + 1) (rescaledSpatialDifference A c ℓ) y =
      ℓ ^ (n + 1) • iteratedFDeriv ℝ (n + 1) A (c + ℓ • y) := by
  let G : CoordinateSpace → F := fun x => A (c + x)
  let D : CoordinateSpace →L[ℝ] CoordinateSpace := ℓ • ContinuousLinearMap.id ℝ CoordinateSpace
  have hG : ContDiff ℝ ∞ G := hA.comp (contDiff_const.add contDiff_id)
  have hn : ((n + 1 : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hD (x : CoordinateSpace) : D x = ℓ • x := rfl
  have hComp : ContDiffAt ℝ (n + 1 : ℕ) (G ∘ D) y :=
    ((hG.comp D.contDiff).contDiffAt).of_le hn
  have hConst : ContDiffAt ℝ (n + 1 : ℕ) (fun _ : CoordinateSpace => -A c) y := contDiffAt_const
  have hzero : iteratedFDeriv ℝ (n + 1) (fun _ : CoordinateSpace => -A c) y = 0 := by
    rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero n)]
    rfl
  have hfun : rescaledSpatialDifference A c ℓ = fun x => (G ∘ D) x + -A c :=
    funext fun _ => sub_eq_add_neg _ _
  rw [hfun, iteratedFDeriv_add_apply' hComp hConst, hzero, add_zero,
    D.iteratedFDeriv_comp_right hG y hn]
  have htranslate : iteratedFDeriv ℝ (n + 1) G (D y) =
      iteratedFDeriv ℝ (n + 1) A (c + ℓ • y) := by
    change iteratedFDeriv ℝ (n + 1) (fun x => A (c + x)) (D y) = _
    rw [iteratedFDeriv_comp_add_left, hD]
  rw [htranslate]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.smul_apply, hD]
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ (n + 1) A (c + ℓ • y)).map_smul_univ (fun _ => ℓ) v

end Burnett.A03
