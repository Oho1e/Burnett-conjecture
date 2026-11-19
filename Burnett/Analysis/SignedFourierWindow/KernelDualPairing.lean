import Burnett.Analysis.SignedFourierWindow.KernelLpExhaustion
import Mathlib.Analysis.Convolution

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Set MeasureTheory
open scoped ENNReal

/-- Transposition for the bilinear (without conjugation) integral. Absolute
integrability follows from the bounded kernel and the two L¹ test functions. -/
theorem kernelApply_bilinear_reflection (K : Space → ℂ) (hK : Continuous K)
    (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D) (f h : Space → ℂ) (mf : Measurable f) (mh : Measurable h)
    (hf : Integrable f) (hh : Integrable h) :
    (∫ x, kernelApply K f x * h x) = ∫ y, f y * kernelApply (fun z => K (-z)) h y := by
  let H (x y : Space) := K (x-y) * f y * h x
  have mH : Measurable (fun z : Space × Space => H z.1 z.2) :=
    ((hK.measurable.comp (measurable_fst.sub measurable_snd)).mul (mf.comp measurable_snd)).mul (mh.comp measurable_fst)
  have prod : Integrable (fun z : Space × Space => H z.1 z.2) (volume.prod volume) := by
    apply ((hh.norm.mul_prod hf.norm).const_mul D).mono' mH.aestronglyMeasurable
    filter_upwards with z
    change ‖K (z.1-z.2) * f z.2 * h z.1‖ ≤ D * (‖h z.1‖ * ‖f z.2‖)
    rw [norm_mul,norm_mul,mul_comm (‖h z.1‖) (‖f z.2‖),←mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hD (z.1-z.2)) (norm_nonneg (f z.2))) (norm_nonneg (h z.1))
  calc
    _ = ∫ x, ∫ y, H x y := by
      apply integral_congr_ae
      filter_upwards with x
      exact (integral_mul_const _ _).symm
    _ = ∫ y, ∫ x, H x y := integral_integral_swap prod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [kernelApply,←integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [H,neg_sub,mul_left_comm,mul_comm]

theorem kernelApply_L1_bounded (K : Space → ℂ) (hK : Integrable K) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D)
    (f : Space → ℂ) (hf : Integrable f) : Integrable (kernelApply K f) ∧
    ∀ x, ‖kernelApply K f x‖ ≤ D * ∫ y, ‖f y‖ := by
  constructor
  · have eq : kernelApply K f = MeasureTheory.convolution f K (ContinuousLinearMap.mul ℂ ℂ) volume := by
      funext x
      apply integral_congr_ae
      filter_upwards with y
      exact mul_comm _ _
    rw [eq]
    exact hf.integrable_convolution (ContinuousLinearMap.mul ℂ ℂ) hK
  · intro x
    calc
      _ ≤ ∫ y, ‖K (x-y) * f y‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ y, D * ‖f y‖ := by
        apply integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
          (hf.norm.const_mul D)
        filter_upwards with y
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right (hD _) (norm_nonneg _)
      _ = _ := integral_const_mul _ _

end Burnett.Analysis.SignedFourierWindow
