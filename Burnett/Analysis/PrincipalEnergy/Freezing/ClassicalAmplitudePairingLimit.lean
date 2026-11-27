import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalAmplitudeLeftRemainderW13
import Burnett.Analysis.TransportWard.Weyl.Amplitude.SchwartzWeylPairingLimit
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeProfileJointSmooth

set_option autoImplicit false
set_option maxHeartbeats 5100000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

private theorem continuous_reduced_action_of_profile
    (F : E → E → E → ℂ) (w : E → ℝ) (h : RadianAmplitudeFourierBounds F w)
    (cF : ∀ η ξ, Continuous (fun x => F x η ξ)) (u : SchwartzMap E ℂ) :
    Continuous (radianLeftQuantization (radianAmplitudeReduced F) u) := by
  let μ : Measure (E × E) := (volume : Measure E).prod (volume : Measure E)
  let G := radianAmplitudeShiftedIntegrand F u
  let W (p : E × E) := (w p.1 * (1+tau*‖p.1‖)) * ((1+tau*‖p.2‖) * ‖𝓕 (u : E → ℂ) p.2‖)
  have eq : radianLeftQuantization (radianAmplitudeReduced F) u = fun x => ∫ p, G x p ∂μ :=
    funext (radian_left_amplitude_reduced_eq_product F w h u)
  have wi : Integrable W μ := h.momentOne.mul_prod (radian_schwartz_fourier_first_moment u)
  have gm (x : E) : AEStronglyMeasurable (G x) μ :=
    (radian_amplitude_shifted_integrable F w h u x).aestronglyMeasurable
  have gb (x : E) : ∀ᵐ p ∂μ, ‖G x p‖ ≤ W p :=
    Eventually.of_forall (radian_amplitude_shifted_integrand_bound F w h u x)
  have gc (p : E × E) : Continuous (fun x => G x p) := by
    have fixed : Continuous (fun _ : E => 𝓕 (u : E → ℂ) p.2) := continuous_const
    exact ((radian_amplitude_phase_base_continuous p.2).mul
      ((radian_amplitude_phase_base_continuous p.1).mul
        (cF p.1 (tau • p.2+tau • p.1)))).mul fixed
  rw [eq]
  exact continuous_of_dominated gm gb wi (Eventually.of_forall gc)

/-- The original physical cutoffs converge in the manuscript's
first-linear Lebesgue pairing against every fixed Schwartz test.
The limiting left action is continuous in the output variable. -/
theorem compact_radian_two_point_pairing_tendsto
    (A : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne A Rx Ry)
    (κ : ℕ → SchwartzMap E ℂ)
    (κB : ∀ n ξ, ‖κ n ξ‖ ≤ 1) (κlimit : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1))
    (u : SchwartzMap E ℂ) :
    let L := radianLeftQuantization (compactRadianReducedAmplitudeSymbol A Rx Ry h) u
    Continuous L ∧ ∀ v : SchwartzMap E ℂ,
      Tendsto (fun n => weylLebesguePairing (radianTwoPointCutoffAction A (κ n) u) v)
        atTop (𝓝 (weylLebesguePairing L v)) := by
  let S := compactRadianTwoPointSlice A Rx Ry h
  let F := radianSchwartzAmplitudeProfile S
  let Fc (n : ℕ) := radianAmplitudeProfileCutoff F (κ n)
  let μ : Measure (E × E) := (volume : Measure E).prod (volume : Measure E)
  obtain ⟨w,hw⟩ := exists_radian_amplitude_fourier_bounds S
    (compact_radian_two_point_slice_order_one A Rx Ry h)
    (compact_radian_two_point_profile_measurable A Rx Ry h)
  have hc (n : ℕ) : RadianAmplitudeFourierBounds (Fc n) w :=
    radian_amplitude_profile_cutoff_bounds F w hw (κ n) (κB n)
  have common (η ξ : E) : Continuous (fun x => F x η ξ) := by
    let arg (x : E) : E × RadianParameter := (η,x,ξ)
    have ca : Continuous arg := continuous_const.prodMk (continuous_id.prodMk continuous_const)
    change Continuous ((fun p : E × RadianParameter =>
      compactRadianParameterProfile A Rx Ry h p.1 p.2) ∘ arg)
    exact (compact_radian_parameter_profile_joint_smooth A Rx Ry h).continuous.comp ca
  refine ⟨continuous_reduced_action_of_profile F w hw common u,fun v => ?_⟩
  let W (p : E × E) := (w p.1 * (1+tau*‖p.1‖)) * ((1+tau*‖p.2‖) * ‖𝓕 (u : E → ℂ) p.2‖)
  have wi : Integrable W μ := hw.momentOne.mul_prod (radian_schwartz_fourier_first_moment u)
  have exactCut (n : ℕ) : radianTwoPointCutoffAction A (κ n) u =
      radianLeftQuantization (radianAmplitudeReduced (Fc n)) u :=
    funext (radian_schwartz_amplitude_cutoff_action_eq_left S w hw (κ n) (κB n) u)
  have measurableCut (n : ℕ) : AEStronglyMeasurable (radianTwoPointCutoffAction A (κ n) u) volume := by
    rw [exactCut n]
    have cj (η ξ : E) : Continuous (fun x => Fc n x η ξ) :=
      continuous_const.mul (common η ξ)
    exact (continuous_reduced_action_of_profile (Fc n) w (hc n) cj u).aestronglyMeasurable
  have bd (n : ℕ) (x : E) : ‖radianTwoPointCutoffAction A (κ n) u x‖ ≤ ∫ p, W p ∂μ := by
    rw [exactCut n,radian_left_amplitude_reduced_eq_product (Fc n) w (hc n) u x]
    apply (norm_integral_le_integral_norm _).trans
    exact integral_mono (radian_amplitude_shifted_integrable (Fc n) w (hc n) u x).norm wi
      (radian_amplitude_shifted_integrand_bound (Fc n) w (hc n) u x)
  exact (schwartz_weyl_pairing_tendsto_of_uniform_output_bound
    (fun n => radianTwoPointCutoffAction A (κ n) u)
    (radianLeftQuantization (radianAmplitudeReduced F) u) measurableCut (∫ p, W p ∂μ) bd
    (compact_radian_two_point_amplitude_cutoff_tendsto_left A Rx Ry h κ κB κlimit u) v).2

end Burnett.A03
