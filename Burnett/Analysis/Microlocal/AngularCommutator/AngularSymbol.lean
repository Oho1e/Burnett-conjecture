import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Smooth homogeneous angular symbols

Uniform degree-zero bounds and rescaled mean-value estimates control the
angular symbol difference at large input frequency.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.AngularCommutator

open Set Metric
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Degree zero for positive dilations of the input frequency. -/
def DegreeZero (m : V → ℂ) : Prop :=
  ∀ (r : ℝ), 0 < r → ∀ x, m (r • x) = m x

private theorem norm_difference_le_local_rescaled
    (m : V → ℂ) (hs : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hh : DegreeZero m) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : V, y ≠ 0 → ‖x - y‖ ≤ ‖y‖ / 2 →
      ‖m x - m y‖ ≤ L * (‖x - y‖ / ‖y‖) := by
  let A : Set V := closedBall 0 (3 / 2) ∩ (ball 0 (1 / 2))ᶜ
  have hA : IsCompact A := (isCompact_closedBall _ _).inter_right isOpen_ball.isClosed_compl
  have hA0 : A ⊆ ({0}ᶜ : Set V) := by
    intro z hz
    have hzb : z ∉ ball (0 : V) (1 / 2) := hz.2
    intro h
    have hz0 : z = 0 := h
    exact hzb (hz0 ▸ mem_ball_self (by norm_num))
  have hfd := (hs.continuousOn_fderiv_of_isOpen isClosed_singleton.isOpen_compl
    (by simp)).mono hA0
  obtain ⟨L, hL, hLbd⟩ := (hA.image_of_continuousOn hfd).isBounded.exists_pos_norm_le
  refine ⟨L, hL.le, ?_⟩
  intro x y hy hnear
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  let r := ‖y‖⁻¹
  have hr : 0 < r := inv_pos.mpr hy'
  have hry : ‖r • y‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_cancel₀ hy'.ne'
  let S := closedBall (r • y) (1 / 2)
  have hSA : S ⊆ A := by
    intro z hz
    have hz' : ‖z - r • y‖ ≤ 1 / 2 := by
      simpa only [S, mem_closedBall, dist_eq_norm] using hz
    have htop : ‖z‖ ≤ ‖z - r • y‖ + 1 := by
      simpa only [sub_add_cancel, hry] using norm_add_le (z - r • y) (r • y)
    have hbottom : 1 ≤ ‖z‖ + ‖z - r • y‖ := by
      have h := norm_add_le (r • y - z) z
      rw [sub_add_cancel, hry, norm_sub_rev (r • y) z] at h
      linarith
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      linarith
    · rw [Set.mem_compl_iff, mem_ball, dist_zero_right, not_lt]
      linarith
  have hscale : ‖r • x - r • y‖ = ‖x - y‖ / ‖y‖ := by
    rw [← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hr, div_eq_mul_inv]
    exact mul_comm _ _
  have hryS : r • y ∈ S := mem_closedBall_self (by norm_num)
  have hrxS : r • x ∈ S := by
    change r • x ∈ closedBall (r • y) (1 / 2)
    rw [mem_closedBall, dist_eq_norm, hscale]
    exact (div_le_iff₀ hy').mpr (by linarith)
  have hd (z : V) (hz : z ∈ S) : DifferentiableAt ℝ m z := by
    exact (hs.contDiffAt
      (isClosed_singleton.isOpen_compl.mem_nhds (hA0 (hSA hz)))).differentiableAt (by simp)
  have hdb (z : V) (hz : z ∈ S) : ‖fderiv ℝ m z‖ ≤ L :=
    hLbd _ (mem_image_of_mem _ (hSA hz))
  have h := (convex_closedBall (r • y) (1 / 2)).norm_image_sub_le_of_norm_fderiv_le
    hd hdb hryS hrxS
  simpa only [hh r hr x, hh r hr y, hscale] using h

/-- Every smooth bounded degree-zero angular symbol has the usual one-sided
difference estimate, including when the output frequency is zero. -/
theorem norm_angular_difference_le
    (m : V → ℂ) (hs : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hh : DegreeZero m)
    (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y : V, y ≠ 0 →
      ‖m x - m y‖ ≤ C * min 1 (‖x - y‖ / ‖y‖) := by
  obtain ⟨L, hL, hnear⟩ := norm_difference_le_local_rescaled m hs hh
  let C := max L (4 * B)
  have hLC : L ≤ C := le_max_left _ _
  have hBC : 4 * B ≤ C := le_max_right _ _
  have hC : 0 ≤ C := hL.trans hLC
  refine ⟨C, hC, ?_⟩
  intro x y hy
  have hy' : 0 < ‖y‖ := norm_pos_iff.mpr hy
  have hbounded : ‖m x - m y‖ ≤ 2 * B :=
    (norm_sub_le _ _).trans (by linarith [hb x, hb y])
  have hlinear : ‖m x - m y‖ ≤ C * (‖x - y‖ / ‖y‖) := by
    by_cases hr : ‖x - y‖ ≤ ‖y‖ / 2
    · exact (hnear x y hy hr).trans (mul_le_mul_of_nonneg_right hLC (by positivity))
    · have hr' : 1 / 2 ≤ ‖x - y‖ / ‖y‖ := (le_div_iff₀ hy').mpr (by linarith)
      calc
        _ ≤ 2 * B := hbounded
        _ ≤ C * (1 / 2) := by linarith
        _ ≤ C * (‖x - y‖ / ‖y‖) := mul_le_mul_of_nonneg_left hr' hC
  rw [mul_min_of_nonneg _ _ hC, le_min_iff, mul_one]
  exact ⟨hbounded.trans (by linarith), hlinear⟩

/-- The actual frequency kernel of multiplication by a cutoff followed by
an angular multiplier commutator has the high-input-frequency majorant. -/
theorem norm_high_input_kernel_le
    (m k : V → ℂ) (hs : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hh : DegreeZero m)
    (B : ℝ) (hb : ∀ x, ‖m x‖ ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ), 0 < R → ∀ x y : V, R ≤ ‖y‖ →
      ‖(m x - m y) * k (x - y)‖ ≤ (C / R) * (‖x - y‖ * ‖k (x - y)‖) := by
  obtain ⟨C, hC, h⟩ := norm_angular_difference_le m hs hh B hb
  refine ⟨C, hC, ?_⟩
  intro R hR x y hy
  have hy0 : 0 < ‖y‖ := hR.trans_le hy
  have hy' : y ≠ 0 := norm_pos_iff.mp hy0
  rw [norm_mul, ← mul_assoc]
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    ‖m x - m y‖ ≤ C * min 1 (‖x - y‖ / ‖y‖) := h x y hy'
    _ ≤ C * (‖x - y‖ / ‖y‖) := mul_le_mul_of_nonneg_left (min_le_right _ _) hC
    _ ≤ C * (‖x - y‖ / R) := mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_left (norm_nonneg _) hR hy) hC
    _ = (C / R) * ‖x - y‖ := by ring

end Burnett.Microlocal.AngularCommutator

namespace Burnett.Microlocal.AngularCommutator

open Set Metric
open scoped ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Uniform global boundedness follows from compactness of the unit sphere and
the fixed complex value assigned at zero. -/
theorem exists_global_bound_of_degreeZero (m : V → ℂ)
    (hs : ContDiffOn ℝ ∞ m ({0}ᶜ : Set V)) (hh : DegreeZero m) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x, ‖m x‖ ≤ B := by
  let S : Set V := sphere 0 1
  have hS : IsCompact S := isCompact_sphere _ _
  have hS0 : S ⊆ ({0}ᶜ : Set V) := by
    intro x hx h
    have he : ‖x‖ = 1 := by simpa only [S, mem_sphere, dist_zero_right] using hx
    have hx0 : x = 0 := h
    simp [hx0] at he
  obtain ⟨A, _, hA⟩ := (hS.image_of_continuousOn (hs.continuousOn.mono hS0)).isBounded.exists_pos_norm_le
  refine ⟨max ‖m 0‖ A, (norm_nonneg _).trans (le_max_left _ _), ?_⟩
  intro x
  by_cases hx : x = 0
  · rw [hx]
    exact le_max_left _ _
  have hnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let r := ‖x‖⁻¹
  have hr : 0 < r := inv_pos.mpr hnorm
  have hxS : r • x ∈ S := by
    change r • x ∈ sphere 0 1
    rw [mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hr]
    exact inv_mul_cancel₀ hnorm.ne'
  calc
    ‖m x‖ = ‖m (r • x)‖ := by rw [hh r hr x]
    _ ≤ A := hA _ (mem_image_of_mem m hxS)
    _ ≤ _ := le_max_right _ _

end Burnett.Microlocal.AngularCommutator
