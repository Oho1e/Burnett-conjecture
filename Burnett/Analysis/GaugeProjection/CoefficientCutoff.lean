import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualCutoff

set_option autoImplicit false
set_option maxHeartbeats 2600000

noncomputable section

namespace Burnett.P01

open Filter Set Metric
open Burnett.A02.FrequencySplit (E mikhlinBall)
open Burnett.A02.FrequencySplit.CMBilinearDual (schwartzBump schwartzBump_apply inputCutoffRadius inputCutoffRadius_pos)
open scoped ContDiff Topology NNReal

private def coefficientBump : SchwartzMap E ℂ := schwartzBump mikhlinBall

private theorem coefficientBump_norm_le (x : E) : ‖coefficientBump x‖ ≤ 1 := by
  rw [coefficientBump, schwartzBump_apply, Complex.norm_real, Real.norm_of_nonneg (mikhlinBall.nonneg)]
  exact mikhlinBall.le_one

private theorem coefficientBump_one {x : E} (h : ‖x‖ ≤ 1) : coefficientBump x = 1 := by
  rw [coefficientBump, schwartzBump_apply, mikhlinBall.one_of_mem_closedBall (mem_closedBall_zero_iff.mpr h),
    Complex.ofReal_one]

private theorem coefficientBump_zero {x : E} (h : 2 ≤ ‖x‖) : coefficientBump x = 0 := by
  rw [coefficientBump, schwartzBump_apply, mikhlinBall.zero_of_le_dist (by simpa only [dist_zero_right] using h),
    Complex.ofReal_zero]

private def coefficientDilation (n : ℕ) : E →L[ℝ] E :=
  (inputCutoffRadius n)⁻¹ • ContinuousLinearMap.id ℝ E

private def smoothCoefficientCutoff (f : E → ℂ) (n : ℕ) (x : E) : ℂ :=
  coefficientBump (coefficientDilation n x) * (f x - f 0)

private theorem smoothCoefficientCutoff_hasCompactSupport (f : E → ℂ) (n : ℕ) :
    HasCompactSupport (smoothCoefficientCutoff f n) := by
  let r := inputCutoffRadius n
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2 * r))
  intro x hx
  by_contra h
  apply hx
  have hr := inputCutoffRadius_pos n
  have hlarge : 2 ≤ ‖coefficientDilation n x‖ := by
    rw [mem_closedBall_zero_iff] at h
    change 2 ≤ ‖r⁻¹ • x‖
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ hr).mpr (le_of_lt (lt_of_not_ge h))
  simp only [smoothCoefficientCutoff, coefficientBump_zero hlarge, zero_mul]

/-- An actual compactly supported coefficient agreeing with the original
coefficient minus its value at zero on an expanding ball. -/
def projectionCoefficientCutoff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) : SchwartzMap E ℂ :=
  (smoothCoefficientCutoff_hasCompactSupport f n).toSchwartzMap
    (((coefficientBump.smooth ⊤).comp (coefficientDilation n).contDiff).mul (hf.sub contDiff_const))

theorem projectionCoefficientCutoff_norm_le (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) (x : E) :
    ‖projectionCoefficientCutoff f hf n x‖ ≤ ‖f x - f 0‖ := by
  change ‖coefficientBump (coefficientDilation n x) * (f x - f 0)‖ ≤ _
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficientBump_norm_le _)

theorem projectionCoefficientCutoff_eventually_eq (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (x : E) :
    ∀ᶠ n : ℕ in atTop, projectionCoefficientCutoff f hf n x = f x - f 0 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hr : ‖x‖ ≤ inputCutoffRadius n := by
    unfold inputCutoffRadius
    exact hN.trans (le_trans (by exact_mod_cast hn) (le_add_of_nonneg_right zero_le_one))
  have hscale := inputCutoffRadius_pos n
  have h : ‖coefficientDilation n x‖ ≤ 1 := by
    change ‖(inputCutoffRadius n)⁻¹ • x‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hscale.le), ← div_eq_inv_mul]
    exact (div_le_one hscale).mpr hr
  change coefficientBump (coefficientDilation n x) * (f x - f 0) = _
  rw [coefficientBump_one h, one_mul]

/-- A constant depending only on the fixed spatial bump. -/
def projectionCoefficientCutoffConstant : ℝ≥0 :=
  1 + (SchwartzMap.seminorm ℝ 1 1 coefficientBump).toNNReal

theorem projectionCoefficientCutoff_lipschitz (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (L : ℝ≥0) (hL : LipschitzWith L f) (n : ℕ) :
    LipschitzWith (projectionCoefficientCutoffConstant * L) (projectionCoefficientCutoff f hf n) := by
  let D := coefficientDilation n
  let χ := coefficientBump
  let r := inputCutoffRadius n
  let S := SchwartzMap.seminorm ℝ 1 1 χ
  have hS : 0 ≤ S := apply_nonneg _ _
  have hr := inputCutoffRadius_pos n
  have hχ (x : E) : ‖χ (D x)‖ ≤ 1 := coefficientBump_norm_le _
  have hpoly (x : E) : ‖f x - f 0‖ ≤ (L : ℝ) * ‖x‖ :=
    by simpa only [sub_zero] using hL.norm_sub_le x 0
  have hDNorm : ‖D‖ ≤ r⁻¹ := by
    change ‖r⁻¹ • ContinuousLinearMap.id ℝ E‖ ≤ r⁻¹
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le), ContinuousLinearMap.norm_id, mul_one]
  apply lipschitzWith_of_nnnorm_fderiv_le (projectionCoefficientCutoff f hf n).differentiable
  intro x
  change ‖fderiv ℝ (smoothCoefficientCutoff f n) x‖ ≤ _
  have hd : HasFDerivAt (fun y => χ (D y)) ((fderiv ℝ χ (D x)).comp D) x :=
    (χ.differentiableAt (x := D x)).hasFDerivAt.comp x D.hasFDerivAt
  have he : HasFDerivAt (fun y => f y - f 0) (fderiv ℝ f x) x := by
    simpa only [sub_zero] using ((hf.differentiable (by norm_num) x).hasFDerivAt).sub
      (hasFDerivAt_const (𝕜 := ℝ) (f 0) x)
  have hg := hd.fun_mul he
  change HasFDerivAt (smoothCoefficientCutoff f n) _ x at hg
  have hweight : ‖D x‖ * ‖fderiv ℝ χ (D x)‖ ≤ S := by
    simpa only [pow_one, ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] using
      χ.le_seminorm ℝ 1 1 (D x)
  have hweight' : ‖x‖ * (‖fderiv ℝ χ (D x)‖ * r⁻¹) ≤ S := by
    have e : ‖D x‖ = r⁻¹ * ‖x‖ := by
      change ‖r⁻¹ • x‖ = _
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
    rw [e] at hweight
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hweight
  have hscaled : ‖(fderiv ℝ χ (D x)).comp D‖ ≤ ‖fderiv ℝ χ (D x)‖ * r⁻¹ :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left hDNorm (norm_nonneg _))
  rw [hg.fderiv]
  calc
    _ ≤ ‖χ (D x) • fderiv ℝ f x‖ +
        ‖(f x - f 0) • (fderiv ℝ χ (D x)).comp D‖ := norm_add_le _ _
    _ ≤ 1 * (L : ℝ) + ((L : ℝ) * ‖x‖) * (‖fderiv ℝ χ (D x)‖ * r⁻¹) := by
      simp only [norm_smul]
      exact add_le_add (mul_le_mul (hχ x) (norm_fderiv_le_of_lipschitz ℝ hL) (norm_nonneg _) zero_le_one)
        (mul_le_mul (hpoly x) hscaled (norm_nonneg _) (by positivity))
    _ = 1 * (L : ℝ) + (L : ℝ) * (‖x‖ * (‖fderiv ℝ χ (D x)‖ * r⁻¹)) := by ring
    _ ≤ 1 * (L : ℝ) + (L : ℝ) * S :=
      add_le_add_left (mul_le_mul_of_nonneg_left hweight' L.2) _
    _ = _ := by
      change _ = (1 + (S.toNNReal : ℝ)) * (L : ℝ)
      rw [Real.coe_toNNReal _ hS]
      ring

end Burnett.P01
