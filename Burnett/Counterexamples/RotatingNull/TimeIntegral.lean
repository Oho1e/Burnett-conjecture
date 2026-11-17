import Burnett.Analysis.IBP.CompactIBP

noncomputable section
namespace Burnett.RotatingNullTime
open MeasureTheory
open scoped ContDiff Topology

theorem cosSin_hasDerivAt (t : ℝ) :
    HasDerivAt (fun s : ℝ => Real.cos s * Real.sin s) (Real.cos (2 * t)) t := by
  convert (Real.hasDerivAt_cos t).mul (Real.hasDerivAt_sin t) using 1
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq t]

theorem time_integral_identity (χ : ℝ → ℝ) (hs : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    (∫ t, deriv χ t * (Real.cos t * Real.sin t)) =
      -(∫ t, χ t * Real.cos (2 * t)) := by
  let F : ℝ → ℝ := fun t => Real.cos t * Real.sin t
  have hF : ContDiff ℝ ∞ F := contDiff_id.cos.mul contDiff_id.sin
  have hDχ : Continuous (fun t => fderiv ℝ χ t (1 : ℝ)) :=
    (hs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDF : Continuous (fun t => fderiv ℝ F t (1 : ℝ)) :=
    (hF.continuous_fderiv (by simp)).clm_apply continuous_const
  have hDFval (t : ℝ) : fderiv ℝ F t (1 : ℝ) = Real.cos (2 * t) := by
    rw [fderiv_deriv]
    exact (cosSin_hasDerivAt t).deriv
  have hi := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume)
    ((hDχ.mul hF.continuous).integrable_of_hasCompactSupport (hc.fderiv_apply ℝ 1).mul_right)
    ((hs.continuous.mul hDF).integrable_of_hasCompactSupport hc.mul_right)
    ((hs.continuous.mul hF.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (hs.differentiable (by simp)) (hF.differentiable (by simp))
  simp_rw [hDFval, fderiv_deriv] at hi
  change (∫ t, deriv χ t * F t) = _
  linarith

end Burnett.RotatingNullTime
