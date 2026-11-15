import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory
open scoped ContDiff

namespace Burnett.X02.CompactIBP

abbrev Space := EuclideanSpace ℝ (Fin 4)

theorem continuous_directional {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (v : Space) :
    Continuous (fun x => fderiv ℝ f x v) :=
  (hf.continuous_fderiv (by simp)).clm_apply continuous_const

/-- All three integrability premises of the Haar IBP theorem are discharged
from actual smoothness and compact support of the test, not assumed. -/
theorem integral_test_directional {φ F : Space → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (hF : ContDiff ℝ ∞ F) (v : Space) :
    (∫ x, φ x * fderiv ℝ F x v) = -(∫ x, fderiv ℝ φ x v * F x) := by
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact ((continuous_directional hφ v).mul hF.continuous).integrable_of_hasCompactSupport
      (hcφ.fderiv_apply ℝ v).mul_right
  · exact (hφ.continuous.mul (continuous_directional hF v)).integrable_of_hasCompactSupport
      hcφ.mul_right
  · exact (hφ.continuous.mul hF.continuous).integrable_of_hasCompactSupport hcφ.mul_right
  · exact hφ.differentiable (by simp)
  · exact hF.differentiable (by simp)

theorem cosine_integral_identity {φ : Space → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (ell : Space →L[ℝ] ℝ) (v : Space) :
    ell v * (∫ x, φ x * Real.cos (ell x)) =
      -(∫ x, fderiv ℝ φ x v * Real.sin (ell x)) := by
  have hd (x : Space) : fderiv ℝ (fun y => Real.sin (ell y)) x v =
      Real.cos (ell x) * ell v := by
    rw [((ell.hasFDerivAt (x := x)).sin).fderiv]
    simp
  have h := integral_test_directional hφ hcφ ell.contDiff.sin v
  simp_rw [hd] at h
  have hi : (fun x => φ x * (Real.cos (ell x) * ell v)) =
      (fun x => ell v * (φ x * Real.cos (ell x))) := by
    funext x
    ring
  rw [hi, integral_const_mul] at h
  exact h

theorem cosine_integral_bound {φ : Space → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    (ell : Space →L[ℝ] ℝ) (v : Space) (hv : ell v ≠ 0) :
    |∫ x, φ x * Real.cos (ell x)| ≤ (∫ x, |fderiv ℝ φ x v|) / |ell v| := by
  have hD := continuous_directional hφ v
  have hDs := hcφ.fderiv_apply ℝ v
  have hsin : ContDiff ℝ ∞ (fun x => Real.sin (ell x)) := ell.contDiff.sin
  have hint : Integrable (fun x => fderiv ℝ φ x v * Real.sin (ell x)) :=
    (hD.mul hsin.continuous).integrable_of_hasCompactSupport hDs.mul_right
  have hiD : Integrable (fun x => |fderiv ℝ φ x v|) :=
    hD.integrable_of_hasCompactSupport hDs |>.abs
  have hbound : |∫ x, fderiv ℝ φ x v * Real.sin (ell x)| ≤
      ∫ x, |fderiv ℝ φ x v| := by
    calc
      _ ≤ ∫ x, ‖fderiv ℝ φ x v * Real.sin (ell x)‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (fun x => fderiv ℝ φ x v * Real.sin (ell x))
      _ ≤ _ := by
        apply integral_mono hint.norm hiD
        intro x
        change ‖fderiv ℝ φ x v * Real.sin (ell x)‖ ≤ |fderiv ℝ φ x v|
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  have hmul : |ell v| * |∫ x, φ x * Real.cos (ell x)| ≤
      ∫ x, |fderiv ℝ φ x v| := by
    rw [← abs_mul, cosine_integral_identity hφ hcφ ell v, abs_neg]
    exact hbound
  apply (le_div_iff₀ (abs_pos.mpr hv)).mpr
  simpa only [mul_comm] using hmul

#print axioms integral_test_directional
#print axioms cosine_integral_bound

end Burnett.X02.CompactIBP
