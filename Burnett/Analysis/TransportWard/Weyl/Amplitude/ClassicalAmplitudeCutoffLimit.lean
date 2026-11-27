import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudePhysicalCutoff

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ENNReal FourierTransform Topology

/-- Genuine exhausting physical cutoff integrals converge on each
Schwartz input to the actual left action of the reduced symbol. The
cutoff is shared by the physical and spectral amplitudes. -/
theorem radian_schwartz_two_point_cutoff_tendsto_left
    (A : E → E → SchwartzMap E ℂ) (w : E → ℝ)
    (H : RadianAmplitudeFourierBounds (radianSchwartzAmplitudeProfile A) w)
    (κ : ℕ → SchwartzMap E ℂ) (κbound : ∀ n ξ, ‖κ n ξ‖ ≤ 1)
    (κlim : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1))
    (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => radianTwoPointCutoffAction (fun a y ζ => A a ζ y) (κ n) u x) atTop
      (𝓝 (radianLeftQuantization (radianAmplitudeReduced (radianSchwartzAmplitudeProfile A)) u x)) := by
  let F := radianSchwartzAmplitudeProfile A
  let Fcut (n : ℕ) := radianAmplitudeProfileCutoff F (κ n)
  let G (n : ℕ) := radianAmplitudeShiftedIntegrand (Fcut n) u x
  let Glimit := radianAmplitudeShiftedIntegrand F u x
  let D (p : E × E) := (w p.1 * (1+tau*‖p.1‖)) * ((1+tau*‖p.2‖) * ‖𝓕 (u : E → ℂ) p.2‖)
  let μ : Measure (E × E) := (volume : Measure E).prod (volume : Measure E)
  have Hcut (n : ℕ) : RadianAmplitudeFourierBounds (Fcut n) w :=
    radian_amplitude_profile_cutoff_bounds F w H (κ n) (κbound n)
  have measurableG (n : ℕ) : AEStronglyMeasurable (G n) μ :=
    (radian_amplitude_shifted_integrable (Fcut n) w (Hcut n) u x).aestronglyMeasurable
  have integrableD : Integrable D μ :=
    H.momentOne.mul_prod (radian_schwartz_fourier_first_moment u)
  have boundG (n : ℕ) : ∀ᵐ p ∂μ, ‖G n p‖ ≤ D p :=
    Eventually.of_forall (radian_amplitude_shifted_integrand_bound (Fcut n) w (Hcut n) u x)
  have limitG : ∀ᵐ p ∂μ, Tendsto (fun n => G n p) atTop (𝓝 (Glimit p)) := by
    filter_upwards with p
    let ζ : E := tau • p.2 + tau • p.1
    have cut : Tendsto (fun n => κ n (tau⁻¹ • ζ) * F x p.1 ζ) atTop (𝓝 (F x p.1 ζ)) := by
      have c : Tendsto (fun _ : ℕ => F x p.1 ζ) atTop (𝓝 (F x p.1 ζ)) := tendsto_const_nhds
      simpa only [one_mul] using (κlim (tau⁻¹ • ζ)).mul c
    have inner := (tendsto_const_nhds (x := patchFourierPhase p.1 x)).mul cut
    have outer := (tendsto_const_nhds (x := patchFourierPhase p.2 x)).mul inner
    exact outer.mul (tendsto_const_nhds (x := 𝓕 (u : E → ℂ) p.2))
  have t := tendsto_integral_of_dominated_convergence D measurableG integrableD boundG limitG
  have cutoff (n : ℕ) :
      radianTwoPointCutoffAction (fun a y ζ => A a ζ y) (κ n) u x = ∫ p, G n p ∂μ :=
    (radian_schwartz_amplitude_cutoff_action_eq_left A w H (κ n) (κbound n) u x).trans
      (radian_left_amplitude_reduced_eq_product (Fcut n) w (Hcut n) u x)
  rw [radian_left_amplitude_reduced_eq_product F w H u x]
  exact t.congr' (Eventually.of_forall fun n => (cutoff n).symm)

end Burnett.A03
