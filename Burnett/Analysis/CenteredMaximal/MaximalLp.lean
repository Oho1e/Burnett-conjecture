import Burnett.Analysis.CenteredMaximal.MaximalStrong

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory
open scoped ENNReal

/-- Strong Lᵖ estimate for the centered maximal function of the absolute value
of a measurable complex function, with the input's actual mathlib Lᵖ seminorm. -/
theorem centeredMax_complex_Lp (f : Space → ℂ) (hf : Measurable f) (p : ℝ) (hp : 1<p) :
    eLpNorm (centeredMax (fun y => ‖f y‖ₑ)) (ENNReal.ofReal p) volume ≤
      maximalConstant p ^ (1/p) * eLpNorm f (ENNReal.ofReal p) volume := by
  have hpos : 0<p := by linarith
  have hn : ENNReal.ofReal p ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm hn ENNReal.ofReal_ne_top,
      eLpNorm_eq_lintegral_rpow_enorm hn ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hpos.le]
  have h := ENNReal.rpow_le_rpow (centeredMax_strong_moment (fun y => ‖f y‖ₑ) hf.enorm p hp)
    (one_div_pos.mpr hpos).le
  rw [ENNReal.mul_rpow_of_nonneg _ _ (one_div_pos.mpr hpos).le] at h
  exact h

end Burnett.Analysis.CenteredMaximal
