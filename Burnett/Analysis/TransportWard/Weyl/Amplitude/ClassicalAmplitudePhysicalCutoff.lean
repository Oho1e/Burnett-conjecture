import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeSpectralAction

set_option autoImplicit false
set_option maxHeartbeats 6300000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform RealInnerProductSpace Topology

private theorem amplitude_tau_pos : 0 < tau :=
  mul_pos (by norm_num) Real.pi_pos

/-- A two-point amplitude reconstructed from its input-variable
Fourier profile. The variable y is the physical input location. -/
def radianAmplitudeOfProfile (F : E → E → E → ℂ) (x y ζ : E) : ℂ :=
  ∫ η : E, patchFourierPhase η y * F x η ζ

/-- Physical oscillatory integral at a genuine Schwartz frequency
cutoff in cycles, with the amplitude evaluated in radians. -/
def radianTwoPointCutoffAction
    (a : E → E → E → ℂ) (κ : SchwartzMap E ℂ) (u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ ξ : E, patchFourierPhase ξ x * κ ξ *
    (∫ y : E, patchFourierPhase (-ξ) y * a x y (tau • ξ) * u y)

/-- Frequency cutoff of the same spectral profile. -/
def radianAmplitudeProfileCutoff (F : E → E → E → ℂ) (κ : SchwartzMap E ℂ) (x η ζ : E) : ℂ :=
  κ (tau⁻¹ • ζ) * F x η ζ

theorem radian_amplitude_profile_cutoff_bounds
    (F : E → E → E → ℂ) (w : E → ℝ) (H : RadianAmplitudeFourierBounds F w)
    (κ : SchwartzMap E ℂ) (hκ : ∀ ξ, ‖κ ξ‖ ≤ 1) :
    RadianAmplitudeFourierBounds (radianAmplitudeProfileCutoff F κ) w := by
  refine ⟨fun x => ?_,H.weightMeasurable,H.weightPositive,H.momentOne,fun x η ζ => ?_⟩
  · have c : Continuous (fun p : E × E => κ (tau⁻¹ • p.2)) :=
      κ.continuous.comp (continuous_const.smul continuous_snd)
    exact c.measurable.mul (H.profileMeasurable x)
  · rw [radianAmplitudeProfileCutoff,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hκ _)).trans (H.valueBound x η ζ)

private theorem radian_amplitude_weight_integrable (F : E → E → E → ℂ) (w : E → ℝ)
    (H : RadianAmplitudeFourierBounds F w) : Integrable w volume := by
  apply H.momentOne.mono' H.weightMeasurable.aestronglyMeasurable
  filter_upwards with η
  rw [Real.norm_of_nonneg (H.weightPositive η)]
  exact le_mul_of_one_le_right (H.weightPositive η)
    (le_add_of_nonneg_right (mul_nonneg amplitude_tau_pos.le (norm_nonneg _)))

theorem radian_fourier_phase_neg_integral (u : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (u : E → ℂ) ξ = ∫ y : E, patchFourierPhase (-ξ) y * u y := by
  rw [Real.fourierIntegral_eq']
  apply integral_congr_ae
  filter_upwards with y
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase,inner_neg_left,smul_eq_mul,real_inner_comm ξ y]
  congr 3; ring

private theorem radian_amplitude_physical_inner
    (F : E → E → E → ℂ) (w : E → ℝ) (H : RadianAmplitudeFourierBounds F w)
    (u : SchwartzMap E ℂ) (x ξ : E) :
    (∫ y : E, patchFourierPhase (-ξ) y * radianAmplitudeOfProfile F x y (tau • ξ) * u y) =
      ∫ η : E, F x η (tau • ξ) * 𝓕 (u : E → ℂ) (ξ-η) := by
  let A := fun y η : E => patchFourierPhase (-ξ) y * (patchFourierPhase η y * F x η (tau • ξ)) * u y
  have c := radian_amplitude_phase_base_continuous (-ξ)
  have k : Measurable (fun η : E => F x η (tau • ξ)) :=
    (H.profileMeasurable x).comp (continuous_id.prodMk (continuous_const : Continuous (fun _ : E => tau • ξ))).measurable
  have am : Measurable (Function.uncurry A) :=
    ((c.measurable.comp measurable_fst).mul ((patch_fourier_phase_continuous.comp
      (continuous_snd.prodMk continuous_fst)).measurable.mul (k.comp measurable_snd))).mul
      (u.continuous.measurable.comp measurable_fst)
  have ai : Integrable (Function.uncurry A) ((volume : Measure E).prod volume) := by
    apply (u.integrable.norm.mul_prod ((radian_amplitude_weight_integrable F w H).mul_const
      (1+‖tau • ξ‖))).mono' am.aestronglyMeasurable
    filter_upwards with p
    simp only [Function.uncurry,A,norm_mul,patch_fourier_phase_norm,one_mul]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (H.valueBound x p.2 (tau • ξ)) (norm_nonneg _)
  calc
    _ = ∫ y : E, ∫ η : E, A y η := by
      apply integral_congr_ae
      filter_upwards with y
      rw [radianAmplitudeOfProfile]
      simp only [A,integral_mul_const,integral_const_mul]
    _ = ∫ η : E, ∫ y : E, A y η := integral_integral_swap ai
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with η
      rw [radian_fourier_phase_neg_integral,← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      dsimp only [A]
      rw [← mul_assoc,← patch_fourier_phase_add]
      have move : -ξ+η = -(ξ-η) := by abel
      rw [move]
      ring

/-- Each physical cutoff of the same amplitude equals the actual left
quantization of the shifted, cutoff profile. Neither the reduced
symbol nor the operator equality is hypothesized. -/
theorem radian_two_point_cutoff_action_eq_left_of_profile
    (F : E → E → E → ℂ) (w : E → ℝ) (H : RadianAmplitudeFourierBounds F w)
    (κ : SchwartzMap E ℂ) (hκ : ∀ ξ, ‖κ ξ‖ ≤ 1) (u : SchwartzMap E ℂ) (x : E) :
    radianTwoPointCutoffAction (radianAmplitudeOfProfile F) κ u x =
      radianLeftQuantization (radianAmplitudeReduced (radianAmplitudeProfileCutoff F κ)) u x := by
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let A := fun ξ η : E => patchFourierPhase ξ x * κ ξ * (F x η (tau • ξ) * U (ξ-η))
  have c := radian_amplitude_phase_frequency_continuous x
  have arg : Continuous (fun p : E × E => (p.2,tau • p.1)) :=
    continuous_snd.prodMk (continuous_const.smul continuous_fst)
  have am : Measurable (Function.uncurry A) :=
    ((c.measurable.comp measurable_fst).mul (κ.continuous.measurable.comp measurable_fst)).mul
      (((H.profileMeasurable x).comp arg.measurable).mul
        (U.continuous.measurable.comp (continuous_fst.sub continuous_snd).measurable))
  let M := SchwartzMap.seminorm ℝ 0 0 U
  have M0 : 0 ≤ M := apply_nonneg _ _
  have ki : Integrable (fun ξ : E => (1+tau*‖ξ‖)*‖κ ξ‖) volume := by
    apply (κ.integrable.norm.add ((κ.integrable_pow_mul volume 1).const_mul tau)).congr
    filter_upwards with ξ
    change ‖κ ξ‖ + tau*(‖ξ‖^1 * ‖κ ξ‖) = (1+tau*‖ξ‖)*‖κ ξ‖
    ring
  have ai : Integrable (Function.uncurry A) ((volume : Measure E).prod volume) := by
    apply ((ki.const_mul M).mul_prod (radian_amplitude_weight_integrable F w H)).mono' am.aestronglyMeasurable
    filter_upwards with p
    simp only [Function.uncurry,A,norm_mul,patch_fourier_phase_norm,one_mul]
    have f := H.valueBound x p.2 (tau • p.1)
    rw [norm_smul,Real.norm_of_nonneg amplitude_tau_pos.le] at f
    calc
      _ ≤ ‖κ p.1‖ * ((w p.2 * (1+tau*‖p.1‖)) * M) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul f (U.norm_le_seminorm ℝ _) (norm_nonneg _)
            (mul_nonneg (H.weightPositive p.2) (by positivity))) (norm_nonneg _)
      _ = _ := by ring
  let D := radianAmplitudeProfileCutoff F κ
  have WB := radian_amplitude_profile_cutoff_bounds F w H κ hκ
  rw [← radian_amplitude_spectral_action_eq_left D w WB u x]
  calc
    _ = ∫ ξ : E, ∫ η : E, A ξ η := by
      rw [radianTwoPointCutoffAction]
      apply integral_congr_ae
      filter_upwards with ξ
      rw [radian_amplitude_physical_inner F w H u x ξ]
      simp only [A,integral_const_mul]
      rfl
    _ = ∫ η : E, ∫ ξ : E, A ξ η := integral_integral_swap ai
    _ = _ := by
      rw [radianAmplitudeSpectralAction]
      apply integral_congr_ae
      filter_upwards with η
      apply integral_congr_ae
      filter_upwards with ξ
      have time : tau⁻¹ • (tau • ξ) = ξ := by
        rw [smul_smul,inv_mul_cancel₀ amplitude_tau_pos.ne',one_smul]
      dsimp only [A,D,radianAmplitudeProfileCutoff]
      rw [time]
      change _ = patchFourierPhase ξ x * (κ ξ * F x η (tau • ξ)) * U (ξ-η)
      ring

/-- The Fourier profile is computed from the actual Schwartz slice of
the input-variable amplitude. -/
def radianSchwartzAmplitudeProfile (A : E → E → SchwartzMap E ℂ) (x η ζ : E) : ℂ :=
  𝓕 (A x ζ : E → ℂ) η

/-- Reconstruction is the genuine Fourier inversion theorem on the
same input slice, including its Fourier normalization. -/
theorem radian_schwartz_amplitude_profile_inversion (A : E → E → SchwartzMap E ℂ) (x y ζ : E) :
    radianAmplitudeOfProfile (radianSchwartzAmplitudeProfile A) x y ζ = A x ζ y := by
  let u := A x ζ
  have eq : radianAmplitudeOfProfile (radianSchwartzAmplitudeProfile A) x y ζ = 𝓕⁻ (𝓕 (u : E → ℂ)) y := by
    rw [radianAmplitudeOfProfile,Real.fourierIntegralInv_eq']
    rfl
  rw [eq]
  exact congrFun (u.continuous.fourier_inversion u.integrable
    (SchwartzMap.fourierTransformCLM ℂ u).integrable) y

/-- The finite physical cutoff reduction for an actual two-point
amplitude whose input slices are Schwartz. -/
theorem radian_schwartz_amplitude_cutoff_action_eq_left
    (A : E → E → SchwartzMap E ℂ) (w : E → ℝ)
    (H : RadianAmplitudeFourierBounds (radianSchwartzAmplitudeProfile A) w)
    (κ : SchwartzMap E ℂ) (hκ : ∀ ξ, ‖κ ξ‖ ≤ 1) (u : SchwartzMap E ℂ) (x : E) :
    radianTwoPointCutoffAction (fun a y ζ => A a ζ y) κ u x =
      radianLeftQuantization (radianAmplitudeReduced
        (radianAmplitudeProfileCutoff (radianSchwartzAmplitudeProfile A) κ)) u x := by
  have eq : (fun a y ζ => A a ζ y) = radianAmplitudeOfProfile (radianSchwartzAmplitudeProfile A) := by
    funext x y ζ
    exact (radian_schwartz_amplitude_profile_inversion A x y ζ).symm
  rw [eq]
  exact radian_two_point_cutoff_action_eq_left_of_profile
    (radianSchwartzAmplitudeProfile A) w H κ hκ u x

end Burnett.A03
