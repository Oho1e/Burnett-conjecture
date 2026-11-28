import Burnett.Analysis.AllScaleTransfer.ActualRadialWindowFourier
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.Microlocal.AngularCommutator (fourier_mul_inverse_eq_integral)
open scoped FourierTransform RealInnerProductSpace

open private radianForm_eq_rescaled from Burnett.Analysis.AllScaleTransfer.ActualRadialWindowFourier

/-- The frequency formula for one inverse-transform factor and two
Schwartz factors uses their actual signed third frequency. -/
private theorem wardInverseFourier_mul_two (F : E → ℂ) (hF : Integrable F)
    (g h : SchwartzMap E ℂ) :
    (∫ x, (𝓕⁻ F) x * g x * h x) =
      ∫ p : Joint, (F p.1 * 𝓕 (g : E → ℂ) p.2) * 𝓕 (h : E → ℂ) (-(p.1+p.2)) := by
  let G := SchwartzMap.fourierTransformCLE ℂ g
  let H := SchwartzMap.fourierTransformCLE ℂ h
  let B : E → ℂ := fun x => h x * g x
  have hInv : (𝓕⁻ (G : E → ℂ)) = (g : E → ℂ) :=
    g.continuous.fourier_inversion g.integrable G.integrable
  have hB : Integrable B :=
    g.integrable.bdd_mul h.continuous.aestronglyMeasurable
      ⟨SchwartzMap.seminorm ℝ 0 0 h, h.norm_le_seminorm ℝ⟩
  have hConv (ξ : E) : 𝓕 B ξ = ∫ q, H (ξ-q) * G q := by
    have hc := fourier_mul_inverse_eq_integral (h : E → ℂ) (G : E → ℂ) h.integrable G.integrable ξ
    rw [hInv] at hc
    exact hc
  have hProd : Integrable (fun p : Joint => (F p.1 * G p.2) * H (-(p.1+p.2)))
      ((volume : Measure E).prod volume) := by
    have hH : Continuous (fun p : Joint => H (-(p.1+p.2))) :=
      H.continuous.comp (continuous_fst.add continuous_snd).neg
    have hFG : Integrable (fun p : Joint => F p.1 * G p.2) ((volume : Measure E).prod volume) :=
      hF.mul_prod G.integrable
    refine (hFG.bdd_mul hH.aestronglyMeasurable
      ⟨SchwartzMap.seminorm ℝ 0 0 H, fun p => H.norm_le_seminorm ℝ (-(p.1+p.2))⟩).congr ?_
    exact Filter.Eventually.of_forall fun _ => mul_comm _ _
  calc
    _ = 𝓕 (fun x => B x * (𝓕⁻ F) x) 0 := by
      rw [Real.fourierIntegral_eq']
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        simp [B]
        ring
    _ = ∫ p, 𝓕 B (0-p) * F p := fourier_mul_inverse_eq_integral B F hB hF 0
    _ = ∫ p, ∫ q, (F p * G q) * H (-(p+q)) := by
      apply integral_congr_ae
      filter_upwards with p
      rw [hConv, ← integral_mul_const]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun q => by
        change H ((0 : E) - p - q) * G q * F p = F p * G q * H (-(p+q))
        have he : (0 : E) - p - q = -(p+q) := by abel
        rw [he]
        ring
    _ = _ := by
      rw [Measure.volume_eq_prod E E]
      exact (integral_prod _ hProd).symm

/-- The scalar order-one action tested against two Schwartz factors
uses the manuscript's radian normalization in both frequencies. -/
theorem wardRadianAction_mul_two_eq_trilinearForm {b : E → ℝ}
    (f g h : SchwartzMap E ℂ) (hf : Integrable (radianActionSpectrum b f)) :
    (∫ x, radianAction b f x * g x * h x) =
      radianTrilinearForm (fun x => (b x.1 : ℂ)) f g h := by
  rw [← radianActionSpectrum_inverse, wardInverseFourier_mul_two _ hf g h, radianForm_eq_rescaled]
  apply integral_congr_ae
  filter_upwards with p
  change ((b (tau • p.1) : ℂ) * 𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2) *
      𝓕 (h : E → ℂ) (-(p.1+p.2)) =
    (b (tau • p.1) : ℂ) * (𝓕 (f : E → ℂ) p.1 * 𝓕 (g : E → ℂ) p.2) *
      𝓕 (h : E → ℂ) (-(p.1+p.2))
  ring

end Burnett.C02
