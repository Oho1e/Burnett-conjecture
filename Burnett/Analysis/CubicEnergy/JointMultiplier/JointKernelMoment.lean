import Burnett.Analysis.CubicEnergy.JointMultiplier.BlockMultiplier

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace

private theorem add_moment (r : ℝ) (hr : 0 ≤ r) (k : ℕ) :
    (1+r)^k ≤ 2^k*(1+r^k) := by
  by_cases h : r ≤ 1
  · calc
      _ ≤ (2:ℝ)^k := by gcongr; linarith
      _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by norm_num : (0:ℝ)≤2) k) (pow_nonneg hr k)]
  · calc
      _ ≤ (2*r)^k := by gcongr; linarith
      _ = 2^k*r^k := mul_pow ..
      _ ≤ _ := by nlinarith [pow_nonneg (by norm_num : (0:ℝ)≤2) k]

private theorem schwartz_moment (K : SchwartzMap Freq8 ℂ) (k : ℕ) :
    Integrable (fun u => (1+‖u‖)^k * ‖K u‖) := by
  have maj := (K.integrable.norm.add (K.integrable_pow_mul volume k)).const_mul ((2:ℝ)^k)
  apply maj.mono' (by fun_prop)
  filter_upwards with u
  change ‖(1+‖u‖)^k * ‖K u‖‖ ≤ 2^k*(‖K u‖+‖u‖^k*‖K u‖)
  rw [Real.norm_of_nonneg (by positivity)]
  exact (mul_le_mul_of_nonneg_right (add_moment _ (norm_nonneg u) k) (norm_nonneg (K u))).trans_eq (by
    ring)

/-- Every separate polynomial translation cost on the two frequency slots is
integrable against the actual inverse Fourier kernel of a smooth joint block. -/
theorem blockKernel_mixed_moment (a : Joint → ℂ) (ha : HasCompactSupport a) (hs : ContDiff ℝ ∞ a)
    (j k : ℕ) :
    Integrable (fun y : Joint => (1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel a y‖) := by
  let A : SchwartzMap Freq8 ℂ :=
    (ha.comp_homeomorph splitFreq.toHomeomorph).toSchwartzMap (hs.comp splitFreq.contDiff)
  let K := (SchwartzMap.fourierTransformCLE ℂ).symm A
  have hK : (K : Freq8 → ℂ) = 𝓕⁻ (fun ξ : Freq8 => a (splitFreq ξ)) :=
    SchwartzMap.fourierTransformCLE_symm_apply _ _
  have hk (y : Joint) : blockKernel a y = K (splitFreq.symm y) := by rw [hK]; rfl
  have mp := splitFreq_preserves_volume.symm splitFreq.toHomeomorph.toMeasurableEquiv
  have hi := mp.integrable_comp_of_integrable (schwartz_moment K (j+k))
  have cont := (blockKernel_integrable a ha hs).2
  apply hi.mono' (by fun_prop)
  filter_upwards with y
  have eq := splitFreq_inner (splitFreq.symm y) (splitFreq.symm y)
  simp only [real_inner_self_eq_norm_sq,ContinuousLinearEquiv.apply_symm_apply] at eq
  have left : ‖y.1‖ ≤ ‖splitFreq.symm y‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith only [eq,sq_nonneg ‖y.2‖])
  have right : ‖y.2‖ ≤ ‖splitFreq.symm y‖ :=
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (by nlinarith only [eq,sq_nonneg ‖y.1‖])
  change ‖(1+‖y.1‖)^j*(1+‖y.2‖)^k*‖blockKernel a y‖‖ ≤ (1+‖splitFreq.symm y‖)^(j+k) * ‖K (splitFreq.symm y)‖
  rw [Real.norm_of_nonneg (by positivity),hk,pow_add]
  gcongr

end Burnett.A02.FrequencySplit
