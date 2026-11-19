import Burnett.Analysis.CubicEnergy.JointMultiplier.BlockMultiplier

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace ContDiff

private def wave (t : ℝ) : ℂ := Complex.exp ((↑(2*Real.pi*t) : ℂ)*Complex.I)

private theorem wave_norm (t : ℝ) : ‖wave t‖ = 1 := by
  simp [wave,Complex.norm_exp]

private theorem wave_cont : Continuous wave := by unfold wave; fun_prop

private theorem wave_add (a b : ℝ) : wave (a+b) = wave a * wave b := by
  unfold wave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def hatTest (f : SchwartzMap E ℂ) : SchwartzMap E ℂ := SchwartzMap.fourierTransformCLM ℂ f

private theorem reconstruct (f : SchwartzMap E ℂ) (x : E) :
    (∫ η, wave (inner ℝ η x) * hatTest f η) = f x := by
  have h := congrFun (f.continuous.fourier_inversion f.integrable (hatTest f).integrable) x
  simpa only [Real.fourierIntegralInv_eq',smul_eq_mul,wave,hatTest] using h

private def carrier (f v : SchwartzMap E ℂ) (x : E) (p : Joint) : ℂ :=
  wave (inner ℝ p.1 x + inner ℝ p.2 x) * (hatTest f p.1 * hatTest v p.2)

private def modulation (s : ℝ) (y p : Joint) : ℂ :=
  wave (- (inner ℝ (s • y.1) p.1 + inner ℝ (s • y.2) p.2))

private theorem shiftedPair (f v : SchwartzMap E ℂ) (x : E) (s : ℝ) (y : Joint) :
    (∫ p, modulation s y p * carrier f v x p) = f (x-s • y.1) * v (x-s • y.2) := by
  rw [← reconstruct f,← reconstruct v,← integral_prod_mul]
  apply integral_congr_ae
  filter_upwards with p
  simp only [modulation,carrier,inner_sub_right]
  rw [show inner ℝ (s • y.1) p.1 = inner ℝ p.1 (s • y.1) from real_inner_comm ..,
      show inner ℝ (s • y.2) p.2 = inner ℝ p.2 (s • y.2) from real_inner_comm ..]
  rw [← mul_assoc,← wave_add]
  rw [show -(inner ℝ p.1 (s • y.1) + inner ℝ p.2 (s • y.2)) +
       (inner ℝ p.1 x + inner ℝ p.2 x) = (inner ℝ p.1 x - inner ℝ p.1 (s • y.1)) +
       (inner ℝ p.2 x - inner ℝ p.2 (s • y.2)) by ring,wave_add]
  ring

private theorem mixed_integrable (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (s : ℝ) (f v : SchwartzMap E ℂ) (x : E) :
    Integrable (Function.uncurry (fun (y p : Joint) => (modulation s y p * blockKernel a y) * carrier f v x p))
      ((volume : Measure Joint).prod volume) := by
  obtain ⟨hi,hc⟩ := blockKernel_integrable a ha hs
  have base : Integrable (fun p : Joint => hatTest f p.1 * hatTest v p.2) := ((hatTest f).integrable.mul_prod (hatTest v).integrable)
  have hmod : Continuous (fun q : Joint × Joint => modulation s q.1 q.2) := by
    unfold modulation
    apply wave_cont.comp
    fun_prop
  have hcarrier : Continuous (carrier f v x) := by
    unfold carrier
    exact (wave_cont.comp (by fun_prop)).mul (((hatTest f).continuous.comp continuous_fst).mul ((hatTest v).continuous.comp continuous_snd))
  refine (hi.norm.mul_prod base.norm).mono' ((hmod.mul (hc.comp continuous_fst)).mul
    (hcarrier.comp continuous_snd)).aestronglyMeasurable ?_
  filter_upwards with q
  rcases q with ⟨y,p⟩
  simp only [Function.uncurry_apply_pair,modulation,carrier,norm_mul,wave_norm,one_mul,le_refl]

/-- Pointwise Fourier formula for the actual dilated bilinear convolution block. -/
theorem block_operator_fourier (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (s : ℝ) (f v : SchwartzMap E ℂ) (x : E) :
    (∫ y : Joint, blockKernel a y * (f (x-s • y.1)*v (x-s • y.2))) =
    ∫ p : Joint, a (s • p) * (Complex.exp ((↑(2*Real.pi*(inner ℝ p.1 x + inner ℝ p.2 x)) : ℂ)*Complex.I)
      * (𝓕 (f : E → ℂ) p.1 * 𝓕 (v : E → ℂ) p.2)) := by
  let T := fun y p : Joint => (modulation s y p * blockKernel a y) * carrier f v x p
  have left (y : Joint) : blockKernel a y * (f (x-s • y.1)*v (x-s • y.2)) = ∫ p, T y p := by
    rw [← shiftedPair f v x s y,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    dsimp only [T]
    ring
  have right (p : Joint) : (∫ y, T y p) = a (s • p) * carrier f v x p := by
    rw [← blockKernel_multiplier a ha hs s p,← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    simp only [T,modulation,wave,mul_neg,neg_mul]
  change _ = ∫ p : Joint, a (s • p) * carrier f v x p
  simp_rw [left,← right]
  exact integral_integral_swap (mixed_integrable a ha hs s f v x)

end Burnett.A02.FrequencySplit
