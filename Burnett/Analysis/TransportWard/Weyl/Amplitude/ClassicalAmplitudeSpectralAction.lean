import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeShift

set_option autoImplicit false
set_option maxHeartbeats 5100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform Topology

/-- The Fourier action of an input-variable amplitude profile. The
frequency seen by the true Schwartz input is shifted by eta. -/
def radianAmplitudeSpectralAction (F : E → E → E → ℂ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ η : E, ∫ ξ : E, patchFourierPhase ξ x * F x η (tau • ξ) * 𝓕 (u : E → ℂ) (ξ-η)

/-- Product integrand in the shifted, absolutely convergent coordinates. -/
def radianAmplitudeShiftedIntegrand
    (F : E → E → E → ℂ) (u : SchwartzMap E ℂ) (x : E) (p : E × E) : ℂ :=
  patchFourierPhase p.2 x * (patchFourierPhase p.1 x * F x p.1 (tau • p.2 + tau • p.1)) *
    𝓕 (u : E → ℂ) p.2

theorem radian_amplitude_shifted_integrand_bound (F : E → E → E → ℂ) (w : E → ℝ)
    (H : RadianAmplitudeFourierBounds F w) (u : SchwartzMap E ℂ) (x : E) (p : E × E) :
    ‖radianAmplitudeShiftedIntegrand F u x p‖ ≤
      (w p.1 * (1+tau*‖p.1‖)) * ((1+tau*‖p.2‖) * ‖𝓕 (u : E → ℂ) p.2‖) := by
  have τ : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  have B : 1+‖tau • p.2 + tau • p.1‖ ≤ (1+tau*‖p.1‖)*(1+tau*‖p.2‖) := by
    have h := norm_add_le (tau • p.2) (tau • p.1)
    rw [norm_smul,norm_smul,Real.norm_of_nonneg τ] at h
    nlinarith only [h,mul_nonneg (mul_nonneg τ (norm_nonneg p.1)) (mul_nonneg τ (norm_nonneg p.2))]
  simp only [radianAmplitudeShiftedIntegrand,norm_mul,patch_fourier_phase_norm,one_mul]
  calc
    _ ≤ w p.1 * (1+‖tau • p.2 + tau • p.1‖) * ‖𝓕 (u : E → ℂ) p.2‖ :=
      mul_le_mul_of_nonneg_right (H.valueBound x p.1 _) (norm_nonneg _)
    _ ≤ (w p.1 * ((1+tau*‖p.1‖)*(1+tau*‖p.2‖))) * ‖𝓕 (u : E → ℂ) p.2‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left B (H.weightPositive p.1)) (norm_nonneg _)
    _ = _ := by ring

theorem radian_schwartz_fourier_first_moment (u : SchwartzMap E ℂ) :
    Integrable (fun ξ : E => (1+tau*‖ξ‖)*‖𝓕 (u : E → ℂ) ξ‖) volume := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  apply (U.integrable.norm.add ((U.integrable_pow_mul volume 1).const_mul tau)).congr
  filter_upwards with ξ
  change ‖U ξ‖ + tau*(‖ξ‖^1 * ‖U ξ‖) = (1+tau*‖ξ‖)*‖U ξ‖
  ring

theorem radian_amplitude_shifted_integrable (F : E → E → E → ℂ) (w : E → ℝ)
    (H : RadianAmplitudeFourierBounds F w) (u : SchwartzMap E ℂ) (x : E) :
    Integrable (radianAmplitudeShiftedIntegrand F u x) ((volume : Measure E).prod volume) := by
  have hP := radian_amplitude_phase_frequency_continuous x
  have arg : Continuous (fun p : E × E => (p.1,tau • p.2 + tau • p.1)) :=
    continuous_fst.prodMk ((continuous_const.smul continuous_snd).add
      (continuous_const.smul continuous_fst))
  let U := SchwartzMap.fourierTransformCLM ℂ u
  have hG : Measurable (radianAmplitudeShiftedIntegrand F u x) :=
    (hP.measurable.comp measurable_snd).mul
      ((hP.measurable.comp measurable_fst).mul ((H.profileMeasurable x).comp arg.measurable)) |>.mul
      (U.continuous.measurable.comp measurable_snd)
  exact (H.momentOne.mul_prod (radian_schwartz_fourier_first_moment u)).mono'
    hG.aestronglyMeasurable (Eventually.of_forall (radian_amplitude_shifted_integrand_bound F w H u x))

/-- Exact integral of the shifted coordinates for the genuine left
Fourier action of the reduced symbol. -/
theorem radian_left_amplitude_reduced_eq_product
    (F : E → E → E → ℂ) (w : E → ℝ) (H : RadianAmplitudeFourierBounds F w)
    (u : SchwartzMap E ℂ) (x : E) :
    radianLeftQuantization (radianAmplitudeReduced F) u x =
      ∫ p : E × E, radianAmplitudeShiftedIntegrand F u x p ∂((volume : Measure E).prod volume) := by
  let G := radianAmplitudeShiftedIntegrand F u x
  have hG : Integrable G ((volume : Measure E).prod volume) :=
    radian_amplitude_shifted_integrable F w H u x
  have hG' : Integrable (Function.uncurry (fun η ξ : E => G (η,ξ))) ((volume : Measure E).prod volume) := hG
  rw [integral_prod G hG,integral_integral_swap hG',radianLeftQuantization]
  apply integral_congr_ae
  filter_upwards with ξ
  change patchFourierPhase ξ x * radianAmplitudeReduced F x (tau • ξ) *
    𝓕 (u : E → ℂ) ξ = ∫ η : E, G (η,ξ)
  simp only [G,radianAmplitudeShiftedIntegrand,radianAmplitudeReduced,integral_mul_const,integral_const_mul]

/-- Actual Fourier translation and Fubini recover the left action from
the original shifted-input spectral integral. -/
theorem radian_amplitude_spectral_action_eq_left
    (F : E → E → E → ℂ) (w : E → ℝ) (H : RadianAmplitudeFourierBounds F w)
    (u : SchwartzMap E ℂ) (x : E) :
    radianAmplitudeSpectralAction F u x = radianLeftQuantization (radianAmplitudeReduced F) u x := by
  let G := radianAmplitudeShiftedIntegrand F u x
  have hG : Integrable G ((volume : Measure E).prod volume) :=
    radian_amplitude_shifted_integrable F w H u x
  rw [radian_left_amplitude_reduced_eq_product F w H u x,integral_prod G hG,radianAmplitudeSpectralAction]
  apply integral_congr_ae
  filter_upwards with η
  calc
    _ = ∫ ξ : E, G (η,ξ-η) := by
      apply integral_congr_ae
      filter_upwards with ξ
      change _ = patchFourierPhase (ξ-η) x * (patchFourierPhase η x *
        F x η (tau • (ξ-η) + tau • η)) * 𝓕 (u : E → ℂ) (ξ-η)
      rw [← smul_add,sub_add_cancel,← mul_assoc,← patch_fourier_phase_add,sub_add_cancel]
    _ = ∫ ξ : E, G (η,ξ) := by
      simpa only [sub_eq_add_neg] using integral_add_right_eq_self (fun ξ => G (η,ξ)) (-η)

end Burnett.A03
