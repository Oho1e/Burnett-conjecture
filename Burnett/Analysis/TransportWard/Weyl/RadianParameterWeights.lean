import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Burnett.A02.FrequencySplit

abbrev RadianParameter := E × E

/-- The usual radian symbol weight. -/
def radianFrequencyWeight (ξ : E) : ℝ := 1+‖ξ‖

theorem radian_frequency_weight_one_le (ξ : E) : 1 ≤ radianFrequencyWeight ξ :=
  le_add_of_nonneg_right (norm_nonneg _)

theorem radian_frequency_weight_pos (ξ : E) : 0 < radianFrequencyWeight ξ :=
  zero_lt_one.trans_le (radian_frequency_weight_one_le ξ)

/-- Test a joint jet with unchanged base directions and scaled radian
frequency directions. The scale is held constant in the jet. -/
def radianParameterScale (s : ℝ) : RadianParameter →L[ℝ] RadianParameter :=
  (ContinuousLinearMap.fst ℝ E E).prod (s • ContinuousLinearMap.snd ℝ E E)

@[simp] theorem radian_parameter_scale_apply (s : ℝ) (p : RadianParameter) :
    radianParameterScale s p = (p.1,s • p.2) := rfl

theorem norm_radian_parameter_scale_le (s : ℝ) :
    ‖radianParameterScale s‖ ≤ max 1 ‖s‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans (le_max_left _ _)) (fun p => ?_)
  rw [radian_parameter_scale_apply,norm_prod_le_iff,norm_smul]
  exact ⟨(norm_fst_le p).trans (le_mul_of_one_le_left (norm_nonneg _) (le_max_left _ _)),
    mul_le_mul (le_max_right _ _) (norm_snd_le p) (norm_nonneg _) (zero_le_one.trans (le_max_left _ _))⟩

@[simp] theorem radian_parameter_scale_mul (s t : ℝ) (p : RadianParameter) :
    radianParameterScale s (radianParameterScale t p) = radianParameterScale (s*t) p := by
  simp only [radian_parameter_scale_apply,smul_smul]

@[simp] theorem radian_parameter_scale_one (p : RadianParameter) : radianParameterScale 1 p = p := by
  simp only [radian_parameter_scale_apply,one_smul,Prod.mk.eta]

theorem radian_frequency_weight_shift_le (ξ q : E) :
    radianFrequencyWeight ξ ≤ (1+‖ξ-q‖)*radianFrequencyWeight q := by
  have tri : ‖ξ‖ ≤ ‖q‖+‖ξ-q‖ := by
    simpa only [add_comm q (ξ-q),sub_add_cancel] using norm_add_le q (ξ-q)
  dsimp only [radianFrequencyWeight]
  nlinarith only [tri,mul_nonneg (norm_nonneg (ξ-q)) (norm_nonneg q)]

end Burnett.A03
