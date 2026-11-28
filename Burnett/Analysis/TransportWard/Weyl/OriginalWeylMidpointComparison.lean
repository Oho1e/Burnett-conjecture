import Burnett.Analysis.TransportWard.Weyl.WindowedWeylKernel
import Burnett.Analysis.TransportWard.Weyl.WindowedWeylLeftAction

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.V03

open Filter MeasureTheory Metric Set Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform Topology

open private windowedWeyl_phase_sub from Burnett.Analysis.TransportWard.Weyl.WindowedWeylKernel
open private radianLeftQuantization_eq_firstOrderAction from Burnett.Analysis.TransportWard.Weyl.WindowedWeylLeftAction

/-- The same regularized Weyl test with the frequency integration first.
The cutoff is expressed in cycles and the symbol itself in radians. -/
def radianMidpointWithCutoff (β : E → E → ℂ) (κ u : SchwartzMap E ℂ) (x : E) : ℂ :=
  ∫ y : E, (∫ ξ : E, patchFourierPhase ξ (x - y) * κ ξ * β ((1 / 2 : ℝ) • (x + y)) (tau • ξ)) * u y

/-- The actual V03 compact Weyl cutoff equals the midpoint integral used
by the spatial Fourier-series comparison on the same Schwartz input. -/
theorem windowedWeyl_physical_cutoff_eq_midpoint (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (χ : SchwartzMap E ℂ) (hχ : ∀ x, χ x = (θ x : ℂ))
    (κ u : SchwartzMap E ℂ) (x : E) :
    radianTwoPointCutoffAction (windowedWeylAmplitude θ β) κ u x =
      (θ x : ℂ) * radianMidpointWithCutoff β κ (scalarSchwartzProduct χ u) x := by
  let a := windowedWeylAmplitude θ β
  let F (p : E × E) := (patchFourierPhase p.1 x * κ p.1) *
    (patchFourierPhase (-p.1) p.2 * a x p.2 (tau • p.1) * u p.2)
  have ha : Continuous (fun p : E × E => a x p.2 (tau • p.1)) := h.jointSmooth.continuous.comp
    (continuous_const.prodMk (continuous_snd.prodMk (continuous_const.smul continuous_fst)))
  have hF : Continuous F :=
    (((patch_fourier_phase_continuous.comp (continuous_fst.prodMk continuous_const)).mul
      (κ.continuous.comp continuous_fst)).mul
      (((patch_fourier_phase_continuous.comp (continuous_fst.neg.prodMk continuous_snd)).mul ha).mul
        (u.continuous.comp continuous_snd)))
  obtain ⟨D, _, hD⟩ := h.orderOneInputDeriv 0
  have hTau : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  have hK : Integrable (fun ξ : E => D * (1 + tau * ‖ξ‖) * ‖κ ξ‖) volume := by
    apply ((κ.integrable.norm.add ((κ.integrable_pow_mul volume 1).const_mul tau)).const_mul D).congr
    filter_upwards with ξ
    simp only [Pi.add_apply, pow_one]
    ring
  have hFI : Integrable F ((volume : Measure E).prod volume) := by
    refine (hK.mul_prod u.integrable.norm).mono' hF.aestronglyMeasurable ?_
    filter_upwards with p
    have he : ‖a x p.2 (tau • p.1)‖ ≤ D * (1 + tau * ‖p.1‖) := by
      simpa only [norm_iteratedFDeriv_zero, norm_smul, Real.norm_of_nonneg hTau] using hD x p.2 (tau • p.1)
    simp only [F, norm_mul, patch_fourier_phase_norm, one_mul]
    calc
      _ ≤ ‖κ p.1‖ * (D * (1 + tau * ‖p.1‖) * ‖u p.2‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right he (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  calc
    _ = ∫ ξ : E, ∫ y : E, F (ξ, y) := by
      unfold radianTwoPointCutoffAction
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [F, a, integral_const_mul]
    _ = ∫ y : E, ∫ ξ : E, F (ξ, y) := integral_integral_swap (f := fun ξ y => F (ξ, y)) hFI
    _ = _ := by
      rw [radianMidpointWithCutoff, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with y
      simp only [scalarSchwartzProduct_apply, hχ, ← integral_mul_const, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [F, a, windowedWeylAmplitude, ← windowedWeyl_phase_sub]
      ring

/-- Any bounded exhausting Schwartz cutoff gives the exact A01 left action
of the same test. This includes the spatial-series midpoint exhaustion. -/
theorem windowedWeyl_midpoint_tendsto_leftAction (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (χ : SchwartzMap E ℂ) (hχ : ∀ x, χ x = (θ x : ℂ))
    (κ : ℕ → SchwartzMap E ℂ) (hκ : ∀ n ξ, ‖κ n ξ‖ ≤ 1)
    (hκLim : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1)) (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => (θ x : ℂ) * radianMidpointWithCutoff β (κ n) (scalarSchwartzProduct χ u) x) atTop
      (𝓝 (firstOrderAction (windowedWeylLeftSymbol θ β R h) u x)) := by
  have left := compact_radian_two_point_amplitude_cutoff_tendsto_left
    (windowedWeylAmplitude θ β) R R h κ hκ hκLim u x
  have hAction := radianLeftQuantization_eq_firstOrderAction
    (windowedWeylLeftRadianSymbol θ β R h) u x
  change Tendsto (fun n => radianTwoPointCutoffAction (windowedWeylAmplitude θ β) (κ n) u x) atTop
    (𝓝 (radianLeftQuantization (windowedWeylLeftRadianSymbol θ β R h) u x)) at left
  rw [hAction] at left
  exact left.congr' (Eventually.of_forall fun n => windowedWeyl_physical_cutoff_eq_midpoint θ β R h χ hχ (κ n) u x)

end Burnett.V03
