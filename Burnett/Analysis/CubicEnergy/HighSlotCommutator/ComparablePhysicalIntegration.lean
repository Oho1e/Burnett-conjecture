import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableFinitePairing
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableCoefficientTestedWindows

set_option autoImplicit false
set_option maxHeartbeats 4100000
noncomputable section
namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal ContDiff BigOperators

private abbrev pairMeasure : Measure (Joint × E) :=
  (volume : Measure Joint).prod (volume : Measure E)

private def comparableTestDensity (A : Joint → ℂ) (s : ℝ)
    (f g h : SchwartzMap E ℂ) (yx : Joint × E) : ℂ :=
  blockKernel A yx.1 * (f (yx.2-s • yx.1.1) * g (yx.2-s • yx.1.2) * h yx.2)

private theorem comparableTestDensity_continuous {A : Joint → ℂ} (hA : Continuous (blockKernel A))
    (s : ℝ) (f g h : SchwartzMap E ℂ) : Continuous (comparableTestDensity A s f g h) := by
  unfold comparableTestDensity
  fun_prop

private theorem comparableTestDensity_integrable {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    Integrable (comparableTestDensity A s f g h) pairMeasure := by
  obtain ⟨hK,hKC⟩ := blockKernel_integrable A ha hA
  have hC := comparableTestDensity_continuous hKC s f g h
  refine ⟨hC.aestronglyMeasurable,?_⟩
  change (∫⁻ yx : Joint × E, ‖comparableTestDensity A s f g h yx‖ₑ ∂pairMeasure) < ⊤
  rw [lintegral_prod _ hC.enorm.aemeasurable]
  letI : ENNReal.HolderTriple 4 4 2 := by
    have hh : (4 : ℝ).HolderTriple 4 2 := ⟨by norm_num,by norm_num,by norm_num⟩
    simpa using hh.ennrealOfReal
  exact (dilated_kernel_trilinear_bound
    (p := 4) (s := 4) (r := 2) (t := 2) (blockKernel A) hKC.measurable f g h s).trans_lt
      (ENNReal.mul_lt_top hK.hasFiniteIntegral
        (ENNReal.mul_lt_top (ENNReal.mul_lt_top (f.eLpNorm_lt_top 4 volume) (g.eLpNorm_lt_top 4 volume))
          (h.eLpNorm_lt_top 2 volume)))

private theorem testedBlock_eq_comparableTestDensity {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (s : ℝ) (f g h : SchwartzMap E ℂ) :
    testedBlock A s f g h = ∫ yx, comparableTestDensity A s f g h yx ∂pairMeasure := by
  rw [integral_prod_symm _ (comparableTestDensity_integrable ha hA s f g h)]
  unfold testedBlock
  apply integral_congr_ae
  filter_upwards with x
  rw [← integral_mul_const]
  apply integral_congr_ae
  filter_upwards with y
  simp only [comparableTestDensity,mul_assoc]

private theorem coe_real_enorm (r : ℝ) : ‖(r : ℂ)‖ₑ = ‖r‖ₑ := by
  rw [← ofReal_norm_eq_enorm,← ofReal_norm_eq_enorm,Complex.norm_real]

private theorem testedBlock_enorm_kernel {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (s : ℝ) (f g h : SchwartzMap E ℂ) :
    ‖s⁻¹ • testedBlock A s f g h‖ₑ ≤
      ∫⁻ y : Joint, ‖blockKernel A y‖ₑ *
        ∫⁻ x : E, ‖s⁻¹‖ₑ * (‖f (x-s • y.1)‖ₑ*‖g (x-s • y.2)‖ₑ*‖h x‖ₑ) := by
  have hK := (blockKernel_integrable A ha hA).2
  have hC : Continuous (fun yx => s⁻¹ • comparableTestDensity A s f g h yx) :=
    continuous_const.smul (comparableTestDensity_continuous hK s f g h)
  rw [testedBlock_eq_comparableTestDensity ha hA,← integral_smul]
  refine (enorm_integral_le_lintegral_enorm _).trans_eq ?_
  rw [lintegral_prod _ hC.enorm.aemeasurable]
  refine lintegral_congr fun y => ?_
  rw [← lintegral_const_mul' _ _ (by finiteness)]
  refine lintegral_congr fun x => ?_
  simp only [comparableTestDensity,Complex.real_smul,enorm_mul,coe_real_enorm]
  ac_rfl

private theorem actual_scaled_coeff_enorm (profile D C : SchwartzMap E ℂ)
    (t : ℝ) (j : ℕ) (x : E)
    (hReal : ∀ p, C p = ((windowTest profile D (dyadicScale t j) p).re : ℂ)) :
    ‖(dyadicScale t j)⁻¹‖ₑ*‖C x‖ₑ = normalizedRealCoefficientAmplitude profile D t j x := by
  simp only [normalizedRealCoefficientAmplitude,enorm_mul,hReal,coe_real_enorm]

/-- In the input-product term the translation moves the actual high output
and leaves the product with the coefficient at its common physical point. -/
theorem comparable_tested_input_integral_le {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (profile D C a e d f g h : SchwartzMap E ℂ) (t l u w : ℝ) (j : ℕ)
    (hReal : ∀ p, C p = ((windowTest profile D (dyadicScale t j) p).re : ℂ)) :
    ‖(dyadicScale t j)⁻¹ • testedBlock A (dyadicScale t j)
      (windowTest d f (l*dyadicScale t j))
      (gapSchwartzProduct C (windowTest a g (u*dyadicScale t j)))
      (windowTest e h (w*dyadicScale t j))‖ₑ ≤
    ∫⁻ y : Joint, ‖blockKernel A y‖ₑ *
      ∫⁻ x : E, normalizedRealCoefficientAmplitude profile D t j x *
        (‖shiftedTest d f l t j (y.1-y.2) x‖ₑ *
          ‖shiftedTest a g u t j 0 x‖ₑ * ‖shiftedTest e h w t j (-y.2) x‖ₑ) := by
  let s := dyadicScale t j
  let F := windowTest d f (l*s)
  let G := windowTest a g (u*s)
  let H := windowTest e h (w*s)
  refine (testedBlock_enorm_kernel ha hA s F (gapSchwartzProduct C G) H).trans_eq ?_
  refine lintegral_congr fun y => congrArg (fun k => ‖blockKernel A y‖ₑ*k) ?_
  let P (x : E) := ‖s⁻¹‖ₑ *
    (‖F (x-s • y.1)‖ₑ*‖gapSchwartzProduct C G (x-s • y.2)‖ₑ*‖H x‖ₑ)
  have hP : Measurable P := by
    dsimp only [P]
    fun_prop
  have tr := (measurePreserving_add_right (volume : Measure E) (s • y.2)).lintegral_comp hP
  change (∫⁻ x, P x) = _
  rw [← tr]
  refine lintegral_congr fun x => ?_
  have hl : x+s • y.2-s • y.1 = x-s • (y.1-y.2) := by rw [smul_sub]; abel
  have hh : x-s • (-y.2) = x+s • y.2 := by rw [smul_neg,sub_neg_eq_add]
  dsimp only [s] at hl hh
  simp only [P,gapSchwartzProduct_apply,add_sub_cancel_right,enorm_mul,hl,shiftedTest,
    smul_zero,sub_zero,s,F,G,H,hh,← actual_scaled_coeff_enorm profile D C t j x hReal]
  ring

/-- In the output-product term the coefficient and its low-pass test already
share a physical point. The remaining annular input has the actual shift. -/
theorem comparable_tested_output_integral_le {A : Joint → ℂ}
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (profile D C a b d f g h : SchwartzMap E ℂ) (t l v u : ℝ) (j : ℕ)
    (hReal : ∀ p, C p = ((windowTest profile D (dyadicScale t j) p).re : ℂ)) :
    ‖(dyadicScale t j)⁻¹ • testedBlock A (dyadicScale t j)
      (windowTest d f (l*dyadicScale t j))
      (windowTest b g (v*dyadicScale t j))
      (gapSchwartzProduct C (windowTest a h (u*dyadicScale t j)))‖ₑ ≤
    ∫⁻ y : Joint, ‖blockKernel A y‖ₑ *
      ∫⁻ x : E, normalizedRealCoefficientAmplitude profile D t j x *
        (‖shiftedTest d f l t j y.1 x‖ₑ *
          ‖shiftedTest b g v t j y.2 x‖ₑ * ‖shiftedTest a h u t j 0 x‖ₑ) := by
  refine (testedBlock_enorm_kernel ha hA _ _ _ _).trans_eq ?_
  refine lintegral_congr fun y => congrArg (fun k => ‖blockKernel A y‖ₑ*k) ?_
  refine lintegral_congr fun x => ?_
  simp only [gapSchwartzProduct_apply,shiftedTest,smul_zero,sub_zero,enorm_mul,
    ← actual_scaled_coeff_enorm profile D C t j x hReal]
  ring

end Burnett.A06
