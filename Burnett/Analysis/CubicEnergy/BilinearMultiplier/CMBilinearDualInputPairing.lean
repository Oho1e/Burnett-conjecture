import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualInputs

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.CenteredMaximal
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

/-- The actual physical pairing with a Schwartz test uses the negative sum
frequency. Both pairings are absolutely integrable for integrable input spectra. -/
theorem jointSpectralBilinear_pairing (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (F G : E → ℂ)
    (hF : Integrable F) (hG : Integrable G) (h : SchwartzMap E ℂ) :
    Integrable (fun x => jointSpectralBilinear m F G x * h x) ∧
      Integrable (fun y : Joint => (m y : ℂ) * F y.1 * G y.2 * 𝓕 (h : E → ℂ) (-(y.1 + y.2))) ∧
      (∫ x, jointSpectralBilinear m F G x * h x) =
        ∫ y : Joint, (m y : ℂ) * F y.1 * G y.2 * 𝓕 (h : E → ℂ) (-(y.1 + y.2)) := by
  let W := fun y : Joint => (m y : ℂ) * (F y.1 * G y.2)
  let P := fun (x : E) (y : Joint) =>
    Complex.exp ((↑(2 * Real.pi * (inner ℝ y.1 x + inner ℝ y.2 x)) : ℂ) * Complex.I)
  let H := SchwartzMap.fourierTransformCLM ℂ h
  have hw : Integrable W := by
    have hi : Integrable (fun y : Joint => F y.1 * G y.2) := hF.mul_prod hG
    exact hi.bdd_mul (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable
      ⟨D, fun y => by simpa only [Function.comp_apply, Complex.norm_real] using hD y⟩
  have np (x : E) (y : Joint) : ‖P x y‖ = 1 := by simp [P, Complex.norm_exp]
  let T := fun (x : E) (y : Joint) => W y * (P x y * h x)
  have hT : Integrable (Function.uncurry T) ((volume : Measure E).prod volume) := by
    have cp : Continuous (fun z : E × Joint => P z.1 z.2) := by dsimp only [P]; fun_prop
    have mw : AEStronglyMeasurable (fun z : E × Joint => W z.2) ((volume : Measure E).prod volume) :=
      hw.1.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
    have mt : AEStronglyMeasurable (Function.uncurry T) ((volume : Measure E).prod volume) :=
      mw.mul (cp.aestronglyMeasurable.mul (h.continuous.comp continuous_fst).aestronglyMeasurable)
    refine (h.integrable.norm.mul_prod hw.norm).mono' mt ?_
    filter_upwards with z
    change ‖W z.2 * (P z.1 z.2 * h z.1)‖ ≤ ‖h z.1‖ * ‖W z.2‖
    simp only [norm_mul, np, one_mul, mul_comm, le_refl]
  have left (x : E) : jointSpectralBilinear m F G x * h x = ∫ y, T x y := by
    rw [jointSpectralBilinear, ← integral_mul_const]
    apply integral_congr_ae
    filter_upwards with y
    change (m y : ℂ) * (P x y * (F y.1 * G y.2)) * h x = W y * (P x y * h x)
    unfold W
    ring
  refine ⟨hT.integral_prod_left.congr (Filter.Eventually.of_forall fun x => (left x).symm), ?_, ?_⟩
  · have cH : Continuous (fun y : Joint => H (-(y.1 + y.2))) :=
      H.continuous.comp (continuous_fst.add continuous_snd).neg
    refine (hw.bdd_mul cH.aestronglyMeasurable ⟨_, fun y => H.norm_le_seminorm ℂ (-(y.1 + y.2))⟩).congr ?_
    filter_upwards with y
    change 𝓕 (h : E → ℂ) (-(y.1 + y.2)) * W y = _
    unfold W
    ring
  have phase_pairing (y : Joint) : (∫ x, P x y * h x) = 𝓕 (h : E → ℂ) (-(y.1 + y.2)) := by
    rw [Real.fourierIntegral_eq']
    apply integral_congr_ae
    filter_upwards with x
    simp only [P, inner_neg_right, inner_add_right, real_inner_comm x y.1, real_inner_comm x y.2,
      smul_eq_mul, neg_mul, mul_neg, neg_neg]
  simp_rw [left]
  rw [integral_integral_swap hT]
  apply integral_congr_ae
  filter_upwards with y
  change (∫ x, W y * (P x y * h x)) = _
  rw [integral_const_mul, phase_pairing]
  unfold W
  ring

end Burnett.A02.FrequencySplit
