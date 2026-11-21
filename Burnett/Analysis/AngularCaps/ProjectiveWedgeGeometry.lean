import Burnett.Analysis.AngularCaps.ProjectiveNullGeometry

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open scoped BigOperators RealInnerProductSpace

/-- The squared Euclidean norm of the exterior product of two covectors.
The ordered coordinate pairs count each unoriented wedge coordinate twice. -/
def coordinateWedgeSq (x y : Vec) : ℝ :=
  (∑ i : Index, ∑ j : Index, (x i * y j - x j * y i)^2)/2

/-- The manuscript's squared projective separation for nonzero covectors. -/
def projectiveWedgeSq (x y : Vec) : ℝ :=
  coordinateWedgeSq x y/(‖x‖^2*‖y‖^2)

theorem coordinateWedgeSq_eq_gram (x y : Vec) :
    coordinateWedgeSq x y = ‖x‖^2*‖y‖^2 - ⟪x, y⟫^2 := by
  have hNorm (u : Vec) : ‖u‖^2 = ∑ i : Index, (u i)^2 := by
    simp only [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  have hInner : ⟪x, y⟫ = ∑ i : Index, x i*y i := by
    rw [PiLp.inner_apply]
    exact Finset.sum_congr rfl fun i _ => by simp [mul_comm]
  have hProd (a b : Index → ℝ) :
      (∑ i, a i)*(∑ j, b j) = ∑ i, ∑ j, a i*b j := by
    rw [Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hExpand : (∑ i : Index, ∑ j : Index, (x i * y j - x j * y i)^2) =
      ∑ i : Index, ∑ j : Index,
        (x i^2*y j^2 + y i^2*x j^2 - 2*(x i*y i*(x j*y j))) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hCross : (∑ i : Index, ∑ j : Index, 2*(x i*y i*(x j*y j))) =
      2*((∑ i : Index, x i*y i)*(∑ j : Index, x j*y j)) := by
    rw [hProd]
    simp only [Finset.mul_sum]
  rw [coordinateWedgeSq, hExpand, hNorm x, hNorm y, hInner]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hCross, ← hProd (fun i => x i^2) (fun j => y j^2),
    ← hProd (fun i => y i^2) (fun j => x j^2)]
  ring

theorem norm_unitRep (x : Vec) (hx : x ≠ 0) : ‖unitRep x‖ = 1 := by
  rw [unitRep, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x)),
    inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]

theorem projectiveWedgeSq_eq_unitRep {x y : Vec} (hx : x ≠ 0) (hy : y ≠ 0) :
    projectiveWedgeSq x y = coordinateWedgeSq (unitRep x) (unitRep y) := by
  rw [projectiveWedgeSq, coordinateWedgeSq_eq_gram, coordinateWedgeSq_eq_gram,
    norm_unitRep x hx, norm_unitRep y hy]
  simp only [unitRep, real_inner_smul_left, real_inner_smul_right]
  field_simp [norm_ne_zero_iff.mpr hx, norm_ne_zero_iff.mpr hy]

theorem projectiveDist_nonneg (x y : Vec) : 0 ≤ projectiveDist x y :=
  le_min (norm_nonneg _) (norm_nonneg _)

theorem projectiveDist_sq_eq_inner {x y : Vec} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    projectiveDist x y^2 = 2*(1 - |⟪x, y⟫|) := by
  have hSub : ‖x-y‖^2 = 2*(1-⟪x, y⟫) := by rw [norm_sub_sq_real, hx, hy]; ring
  have hAdd : ‖x+y‖^2 = 2*(1+⟪x, y⟫) := by rw [norm_add_sq_real, hx, hy]; ring
  by_cases h : 0 ≤ ⟪x, y⟫
  · have hle : ‖x-y‖ ≤ ‖x+y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by linarith only [h, hSub, hAdd])
    rw [projectiveDist, min_eq_left hle, abs_of_nonneg h, hSub]
  · have hle : ‖x+y‖ ≤ ‖x-y‖ :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
        (by linarith only [lt_of_not_ge h, hSub, hAdd])
    rw [projectiveDist, min_eq_right hle, abs_of_neg (lt_of_not_ge h), hAdd]
    ring

/-- Uniform angle comparison on the unit sphere, including opposite lifts. -/
theorem coordinateWedgeSq_compare_projectiveDist {x y : Vec} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) :
    projectiveDist x y^2 / 2 ≤ coordinateWedgeSq x y ∧
      coordinateWedgeSq x y ≤ projectiveDist x y^2 := by
  have hA : |⟪x, y⟫| ≤ 1 := by simpa only [hx, hy, mul_one] using abs_real_inner_le_norm x y
  have hN := abs_nonneg ⟪x, y⟫
  have hL := mul_nonneg hN (sub_nonneg.mpr hA)
  have hU := sq_nonneg (1 - |⟪x, y⟫|)
  rw [coordinateWedgeSq_eq_gram, hx, hy, projectiveDist_sq_eq_inner hx hy,
    ← sq_abs ⟪x, y⟫]
  constructor <;> nlinarith only [hL, hU]

theorem projectiveWedgeSq_neg_left (x y : Vec) : projectiveWedgeSq (-x) y = projectiveWedgeSq x y := by
  simp [projectiveWedgeSq, coordinateWedgeSq_eq_gram]

theorem projectiveWedgeSq_neg_right (x y : Vec) : projectiveWedgeSq x (-y) = projectiveWedgeSq x y := by
  simp [projectiveWedgeSq, coordinateWedgeSq_eq_gram]

end Burnett.Analysis.ProjectiveNullCaps
