import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowPairing
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointKernelMoment

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory Finset
open scoped ENNReal ContDiff

def translatedEntry (r : ℝ) (f g h : SchwartzMap E ℂ) (y : Joint) (x : E) : ℂ :=
  f (x-r • y.1)*g (x-r • y.2)*h x

private theorem continuous_translated (r : ℝ) (f g h : SchwartzMap E ℂ) :
    Continuous (Function.uncurry (translatedEntry r f g h)) := by
  change Continuous (fun p : Joint × E => f (p.2-r • p.1.1)*g (p.2-r • p.1.2)*h p.2)
  fun_prop

private theorem one_bound (A : Joint → ℂ) (hK : Continuous (blockKernel A)) (r : ℝ)
    (f g h : SchwartzMap E ℂ) :
    ‖testedBlock A r f g h‖ₑ ≤ ∫⁻ y : Joint, ∫⁻ x : E, ‖blockKernel A y‖ₑ*
      ‖translatedEntry r f g h y x‖ₑ := by
  let U := fun (x : E) (y : Joint) => blockKernel A y*translatedEntry r f g h y x
  have co : Continuous (Function.uncurry U) := (hK.comp continuous_snd).mul
    ((continuous_translated r f g h).comp continuous_swap)
  have eq : testedBlock A r f g h = ∫ x,∫ y,U x y := by
    unfold testedBlock
    apply integral_congr_ae
    filter_upwards with x
    rw [← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp only [U,translatedEntry,mul_assoc]
  rw [eq]
  calc
    _ ≤ ∫⁻ x,∫⁻ y,‖U x y‖ₑ := (enorm_integral_le_lintegral_enorm _).trans
      (lintegral_mono fun x => enorm_integral_le_lintegral_enorm _)
    _ = ∫⁻ y,∫⁻ x,‖U x y‖ₑ := lintegral_lintegral_swap co.measurable.enorm.aemeasurable
    _ = _ := by simp only [U,enorm_mul]

/-- The finite spatial sum has a single common reference kernel. The inner
sum uses absolute values before integration, so it can be bounded by the two
square functions at each kernel translation. -/
theorem testedBlocks_enorm_le (A : Joint → ℂ) (ha : HasCompactSupport A) (hs : ContDiff ℝ ∞ A)
    (n : ℕ) (r : Fin n → ℝ) (f g h : Fin n → SchwartzMap E ℂ) :
    ‖∑ i, testedBlock A (r i) (f i) (g i) (h i)‖ₑ ≤
      ∫⁻ y : Joint, ‖blockKernel A y‖ₑ*(∫⁻ x : E, ∑ i, ‖translatedEntry (r i) (f i) (g i) (h i) y x‖ₑ) := by
  let K := blockKernel A
  let U := fun i : Fin n => translatedEntry (r i) (f i) (g i) (h i)
  have mc (i : Fin n) : Measurable (Function.uncurry (U i)) := (continuous_translated ..).measurable
  have ck : Continuous K := (blockKernel_integrable A ha hs).2
  have one (i : Fin n) : ‖testedBlock A (r i) (f i) (g i) (h i)‖ₑ ≤
      ∫⁻ y : Joint, ‖K y‖ₑ * ∫⁻ x : E, ‖U i y x‖ₑ := by
    refine (one_bound A ck (r i) (f i) (g i) (h i)).trans_eq ?_
    apply lintegral_congr
    intro y
    exact lintegral_const_mul' _ _ (by finiteness)
  calc
    _ ≤ ∑ i, ‖testedBlock A (r i) (f i) (g i) (h i)‖ₑ := enorm_sum_le _ _
    _ ≤ ∑ i, ∫⁻ y : Joint, ‖K y‖ₑ*∫⁻ x : E, ‖U i y x‖ₑ := sum_le_sum (fun i _ => one i)
    _ = ∫⁻ y : Joint, ∑ i, ‖K y‖ₑ*∫⁻ x : E, ‖U i y x‖ₑ := by
      rw [lintegral_finset_sum]
      intro i _
      have inner : Measurable (fun y : Joint => ∫⁻ x : E, ‖U i y x‖ₑ) :=
        (mc i).enorm.lintegral_prod_right'
      exact ck.measurable.enorm.mul inner
    _ = _ := by
      apply lintegral_congr
      intro y
      rw [← mul_sum,lintegral_finset_sum]
      intro i _
      exact ((mc i).comp ((measurable_const (a := y)).prodMk measurable_id)).enorm

end Burnett.A02.FrequencySplit
