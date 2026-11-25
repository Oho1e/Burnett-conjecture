import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowPairing

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped FourierTransform RealInnerProductSpace

private theorem reverse_shift_le (x y : E) : ‖x‖ ≤ ‖x-y‖ + ‖y‖ := by
  calc
    ‖x‖ = ‖(x-y)+y‖ := by rw [sub_add_cancel]
    _ ≤ _ := norm_add_le _ _

/-- The same low coefficient cannot move the high input or high output out of
bounded annuli when its frequency is small compared with the lower edge. -/
theorem lowCoefficient_shifted_annuli {p q z : E} {a b ρ ε : ℝ}
    (ha : 0 < a) (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (he : ε < (1-ρ)*a) (hq : a ≤ ‖q‖ ∧ ‖q‖ ≤ b)
    (hp : ‖p‖ ≤ ρ*‖q‖) (hz : ‖z‖ ≤ ε) :
    0 < a-ε ∧ 0 < (1-ρ)*a-ε ∧ ‖p‖ ≤ ρ*b ∧
    (a-ε ≤ ‖q-z‖ ∧ ‖q-z‖ ≤ b+ε) ∧
    ((1-ρ)*a-ε ≤ ‖p+q-z‖ ∧ ‖p+q-z‖ ≤ (1+ρ)*b+ε) := by
  have pos : 0 ≤ 1-ρ := sub_nonneg.mpr hρ'.le
  have houtlo : (1-ρ)*‖q‖ ≤ ‖p+q‖ := by
    have h := reverse_shift_le q (-p)
    rw [sub_neg_eq_add, add_comm q p, norm_neg] at h
    linarith only [h,hp]
  have houthi : ‖p+q‖ ≤ (1+ρ)*‖q‖ := by linarith only [norm_add_le p q,hp]
  have hmin := (mul_le_mul_of_nonneg_left hq.1 pos).trans houtlo
  have hmax := houthi.trans (mul_le_mul_of_nonneg_left hq.2 (by positivity))
  refine ⟨?_,sub_pos.mpr he,hp.trans (mul_le_mul_of_nonneg_left hq.2 hρ),⟨?_,?_⟩,?_⟩
  · linarith only [he,mul_nonneg hρ ha.le]
  · linarith only [reverse_shift_le q z,hq.1,hz]
  · linarith only [norm_sub_le q z,hq.2,hz]
  · exact ⟨by linarith only [reverse_shift_le (p+q) z,hmin,hz],
      by linarith only [norm_sub_le (p+q) z,hmax,hz]⟩

private def phase (x q : E) : ℂ :=
  Complex.exp ((↑(-2*Real.pi*inner ℝ x q) : ℂ)*Complex.I)

private theorem phase_norm (x q : E) : ‖phase x q‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

private theorem phase_sub (x q z : E) : phase x (q-z) = phase x q * phase x (-z) := by
  unfold phase
  rw [← Complex.exp_add,inner_sub_right,inner_neg_right]
  congr 1
  push_cast
  ring

/-- Fourier convolution for the pointwise product of the actual Schwartz
factors, with the same Fourier convention as the spatial window operators. -/
theorem fourier_schwartz_product_coeff (c g : SchwartzMap E ℂ) (q : E) :
    𝓕 (fun x : E => c x * g x) q =
      ∫ z : E, 𝓕 (c : E → ℂ) z * 𝓕 (g : E → ℂ) (q-z) := by
  let C := SchwartzMap.fourierTransformCLM ℂ c
  let K := fun (x z : E) => C z * (phase x (q-z) * g x)
  have cc (x : E) : c x = ∫ z : E, phase x (-z) * C z := by
    have inv := congrFun (c.continuous.fourier_inversion c.integrable C.integrable) x
    change 𝓕⁻ (C : E → ℂ) x = c x at inv
    rw [← inv,Real.fourierIntegralInv_eq']
    apply integral_congr_ae
    filter_upwards with z
    simp only [phase,inner_neg_right,real_inner_comm z x, mul_neg, neg_mul,neg_neg,smul_eq_mul]
  have hK : Integrable (Function.uncurry K) ((volume : Measure E).prod volume) := by
    have cont : Continuous (Function.uncurry K) := by unfold K phase Function.uncurry; fun_prop
    refine (g.integrable.norm.mul_prod C.integrable.norm).mono' cont.aestronglyMeasurable ?_
    filter_upwards with y
    change ‖K y.1 y.2‖ ≤ ‖g y.1‖ * ‖C y.2‖
    simp only [K,norm_mul,phase_norm,one_mul,mul_comm,le_refl]
  have hx (x : E) : phase x q * (c x * g x) = ∫ z : E, K x z := by
    rw [cc x,← integral_mul_const,← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with z
    change _ = C z * (phase x (q-z) * g x)
    rw [phase_sub]
    ring
  rw [Real.fourierIntegral_eq']
  change (∫ x, phase x q * (c x * g x)) = _
  simp_rw [hx]
  rw [integral_integral_swap hK]
  apply integral_congr_ae
  filter_upwards with z
  change (∫ x, C z * (phase x (q-z) * g x)) = _
  rw [integral_const_mul,Real.fourierIntegral_eq' (g : E → ℂ)]
  rfl

/-- A compact Fourier support for the actual coefficient permits changing
the other input on just the corresponding shifted set of frequencies. -/
theorem fourier_schwartz_product_replace (c g G : SchwartzMap E ℂ) (q : E)
    (h : ∀ z : E, 𝓕 (c : E → ℂ) z ≠ 0 →
      𝓕 (g : E → ℂ) (q-z) = 𝓕 (G : E → ℂ) (q-z)) :
    𝓕 (fun x : E => c x * g x) q = 𝓕 (fun x : E => c x * G x) q := by
  rw [fourier_schwartz_product_coeff, fourier_schwartz_product_coeff]
  apply integral_congr_ae
  filter_upwards with z
  by_cases he : 𝓕 (c : E → ℂ) z = 0
  · simp only [he,zero_mul]
  · rw [h z he]

end Burnett.A06
