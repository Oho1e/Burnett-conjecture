import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianLeftQuantizationAlgebra

set_option autoImplicit false
set_option maxHeartbeats 4200000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform Topology

private theorem amplitude_tau_nonneg : 0 ≤ tau :=
  mul_nonneg (by norm_num) Real.pi_pos.le

theorem radian_amplitude_phase_frequency_continuous (x : E) :
    Continuous (fun η : E => patchFourierPhase η x) := by
  let args (η : E) : E × E := (η,x)
  change Continuous ((fun p : E × E => patchFourierPhase p.1 p.2) ∘ args)
  exact patch_fourier_phase_continuous.comp (continuous_id.prodMk continuous_const)

theorem radian_amplitude_phase_base_continuous (η : E) :
    Continuous (fun x : E => patchFourierPhase η x) := by
  let args (x : E) : E × E := (η,x)
  change Continuous ((fun p : E × E => patchFourierPhase p.1 p.2) ∘ args)
  exact patch_fourier_phase_continuous.comp (continuous_const.prodMk continuous_id)

/-- Moving by a frequency offset costs only a polynomial of that offset
in a standard symbol weight. The first derivative then gives the gain
of one order in the diagonal-to-left shift. -/
theorem weighted_frequency_shift_sub_bound {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] (F : E → V) (n : ℕ) (w : ℝ)
    (hF : Differentiable ℝ F)
    (d : ∀ q, (1+‖q‖)^n * ‖fderiv ℝ F q‖ ≤ w) (ξ v : E) :
    (1+‖ξ‖)^n * ‖F (ξ+v) - F ξ‖ ≤ (1+‖v‖)^n * w * ‖v‖ := by
  let B := closedBall ξ ‖v‖
  have sx : ξ ∈ B := mem_closedBall_self (norm_nonneg _)
  have sy : ξ + v ∈ B := by
    simp [B,mem_closedBall,dist_eq_norm]
  have positive : 0 < (1+‖ξ‖)^n := by positivity
  have grad (q : E) (hq : q ∈ B) :
      ‖fderiv ℝ F q‖ ≤ ((1+‖v‖)^n * w) / (1+‖ξ‖)^n := by
    apply (le_div_iff₀ positive).mpr
    have qdist : ‖ξ-q‖ ≤ ‖v‖ := by
      rw [← dist_eq_norm, dist_comm]
      exact hq
    have addQ : ‖ξ‖ ≤ ‖q‖ + ‖v‖ := by
      exact calc
        ‖ξ‖ = ‖q + (ξ-q)‖ := by congr 1; abel
        _ ≤ ‖q‖ + ‖ξ-q‖ := norm_add_le _ _
        _ ≤ ‖q‖ + ‖v‖ := add_le_add_left qdist _
    have weight : 1+‖ξ‖ ≤ (1+‖v‖)*(1+‖q‖) := by
      nlinarith only [addQ, mul_nonneg (norm_nonneg v) (norm_nonneg q)]
    have power := pow_le_pow_left₀ (show 0 ≤ 1+‖ξ‖ by positivity) weight n
    rw [mul_pow] at power
    calc
      _ = (1+‖ξ‖)^n * ‖fderiv ℝ F q‖ := by ring
      _ ≤ ((1+‖v‖)^n * (1+‖q‖)^n) * ‖fderiv ℝ F q‖ :=
        mul_le_mul_of_nonneg_right power (norm_nonneg _)
      _ = (1+‖v‖)^n * ((1+‖q‖)^n * ‖fderiv ℝ F q‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (d q) (by positivity)
  have lip := Convex.norm_image_sub_le_of_norm_fderiv_le (fun x _ => hF x) grad
    (convex_closedBall ξ ‖v‖) sx sy
  have subtract : ξ+v-ξ = v := by abel
  rw [subtract] at lip
  exact (mul_le_mul_of_nonneg_left lip positive.le).trans_eq (by
    rw [← mul_assoc, mul_div_cancel₀ _ positive.ne'])

/-- First moment and ordinary order-one growth of the actual Fourier
profiles in the input base variable. The profile is in cycles for eta
and radians for zeta. -/
structure RadianAmplitudeFourierBounds (F : E → E → E → ℂ) (w : E → ℝ) : Prop where
  profileMeasurable : ∀ x, Measurable (fun q : E × E => F x q.1 q.2)
  weightMeasurable : Measurable w
  weightPositive : ∀ η, 0 ≤ w η
  momentOne : Integrable (fun η => w η * (1+tau*‖η‖)) volume
  valueBound : ∀ x η ζ, ‖F x η ζ‖ ≤ w η * (1+‖ζ‖)

/-- The diagonal symbol obtained from the Fourier profile of the
two-point amplitude. -/
def radianAmplitudeDiagonal (F : E → E → E → ℂ) (x ζ : E) : ℂ :=
  ∫ η : E, patchFourierPhase η x * F x η ζ

/-- The actual shifted spectral reduction in the same Fourier
normalization as radianLeftQuantization. -/
def radianAmplitudeReduced (F : E → E → E → ℂ) (x ζ : E) : ℂ :=
  ∫ η : E, patchFourierPhase η x * F x η (ζ+tau • η)

theorem radian_amplitude_spectral_integrable
    (F : E → E → E → ℂ) (w : E → ℝ)
    (H : RadianAmplitudeFourierBounds F w) (x ζ : E) (t : ℝ) (ht : 0 ≤ t) (htau : t ≤ tau) :
    Integrable (fun η : E => patchFourierPhase η x * F x η (ζ+t • η)) volume := by
  have args : Continuous (fun η : E => (η,ζ+t • η)) :=
    continuous_id.prodMk (continuous_const.add (continuous_const.smul continuous_id))
  have phase := radian_amplitude_phase_frequency_continuous x
  apply (H.momentOne.const_mul (1+‖ζ‖)).mono'
    (phase.aestronglyMeasurable.mul ((H.profileMeasurable x).comp args.measurable).aestronglyMeasurable)
  filter_upwards with η
  change ‖patchFourierPhase η x * F x η (ζ+t • η)‖ ≤ _
  rw [norm_mul,patch_fourier_phase_norm,one_mul]
  apply (H.valueBound x η (ζ+t • η)).trans
  have normB : ‖ζ+t • η‖ ≤ ‖ζ‖+tau*‖η‖ := by
    apply (norm_add_le _ _).trans
    rw [norm_smul,Real.norm_of_nonneg ht]
    exact add_le_add_left (mul_le_mul_of_nonneg_right htau (norm_nonneg _)) _
  calc
    _ ≤ w η * (1+(‖ζ‖+tau*‖η‖)) :=
      mul_le_mul_of_nonneg_left (add_le_add_left normB 1) (H.weightPositive η)
    _ ≤ (1+‖ζ‖) * (w η * (1+tau*‖η‖)) := by
      calc
        _ ≤ w η * ((1+‖ζ‖)*(1+tau*‖η‖)) :=
          mul_le_mul_of_nonneg_left (by
            nlinarith only [mul_nonneg (norm_nonneg ζ) (mul_nonneg amplitude_tau_nonneg (norm_nonneg η))])
            (H.weightPositive η)
        _ = _ := by ring

/-- First remainder of the actual spectral reduction at function level.
For higher seminorms, the same weighted shift estimate applies to the
differentiated profiles. -/
theorem radian_amplitude_reduced_sub_diagonal_value_bound
    (F : E → E → E → ℂ) (w : E → ℝ) (H : RadianAmplitudeFourierBounds F w)
    (hF : ∀ x η, Differentiable ℝ (F x η))
    (d : ∀ x η q, ‖fderiv ℝ (F x η) q‖ ≤ w η) (x ζ : E) :
    ‖radianAmplitudeReduced F x ζ - radianAmplitudeDiagonal F x ζ‖ ≤
      ∫ η : E, w η * (tau*‖η‖) := by
  have regular := radian_amplitude_spectral_integrable F w H x ζ tau amplitude_tau_nonneg le_rfl
  have diag : Integrable (fun η : E => patchFourierPhase η x * F x η ζ) volume := by
    simpa only [zero_smul,add_zero] using
      radian_amplitude_spectral_integrable F w H x ζ 0 le_rfl amplitude_tau_nonneg
  rw [radianAmplitudeReduced,radianAmplitudeDiagonal,← integral_sub regular diag]
  apply (norm_integral_le_integral_norm _).trans
  have wMeas : AEStronglyMeasurable (fun η => w η*(tau*‖η‖)) volume := by
    exact (H.weightMeasurable.mul (continuous_const.mul continuous_norm).measurable).aestronglyMeasurable
  have weight : Integrable (fun η => w η*(tau*‖η‖)) volume := by
    refine H.momentOne.mono' wMeas (Eventually.of_forall fun η => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (H.weightPositive η)
      (mul_nonneg amplitude_tau_nonneg (norm_nonneg _)))]
    exact mul_le_mul_of_nonneg_left (by linarith) (H.weightPositive η)
  apply integral_mono_ae (regular.sub diag).norm weight
  filter_upwards with η
  change ‖patchFourierPhase η x * F x η (ζ+tau • η) - patchFourierPhase η x * F x η ζ‖ ≤ _
  rw [← mul_sub,norm_mul,patch_fourier_phase_norm,one_mul]
  have h := weighted_frequency_shift_sub_bound (F x η) 0 (w η)
    (hF x η) (fun q => by simpa only [pow_zero,one_mul] using d x η q) ζ (tau • η)
  simpa only [pow_zero,one_mul,norm_smul,Real.norm_of_nonneg amplitude_tau_nonneg] using h

end Burnett.A03
