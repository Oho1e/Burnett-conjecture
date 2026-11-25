import Burnett.Analysis.Fourier.RadianCoordinateDerivative
import Burnett.Analysis.Fourier.FixedInfraredSchwartz
import Burnett.Analysis.GaugeProjection.GaugeProjectionLp

set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.CenteredMaximal (maximalConstant maximalConstant_finite)
open Burnett.Analysis.HminusWeightedDual (fourier_pderiv)
open Burnett.A02.FrequencySplit (E windowTest windowTest_fourier windowTest_translate)
open Burnett.A07 (coordinateDerivative fixedInfraredSchwartz)
open Burnett.P01 (projectionInfraredAction gaugeProjectionInfrared gaugeProjectionInfrared_contDiff
  gaugeProjectionInfrared_zero gaugeProjectionInfrared_one)
open private lowInfraredSchwartz from Burnett.Analysis.Fourier.FixedInfraredSchwartz
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace Topology

/-- Fourier profile of the derivative of the actual inverse Fourier window. -/
private def derivativeWindow (b : Fin 4) (φ : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.fourierTransformCLE ℂ (coordinateDerivative b ((SchwartzMap.fourierTransformCLE ℂ).symm φ))

private theorem derivativeWindow_apply (b : Fin 4) (φ : SchwartzMap E ℂ) (ξ : E) :
    derivativeWindow b φ ξ = (2 * Real.pi * Complex.I) *
      (inner ℝ ξ (EuclideanSpace.single b 1) : ℂ) * φ ξ := by
  unfold derivativeWindow coordinateDerivative
  change 𝓕 (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single b 1)
    ((SchwartzMap.fourierTransformCLE ℂ).symm φ) : E → ℂ) ξ = _
  rw [fourier_pderiv]
  have h := congrArg (fun ψ : SchwartzMap E ℂ => ψ ξ)
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply φ)
  rw [show 𝓕 ((SchwartzMap.fourierTransformCLE ℂ).symm φ : E → ℂ) ξ = φ ξ from h]

private theorem coordinateDerivative_windowTest_one (b : Fin 4) (φ f : SchwartzMap E ℂ) :
    coordinateDerivative b (windowTest φ f 1) = windowTest (derivativeWindow b φ) f 1 := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ξ
  change 𝓕 (coordinateDerivative b (windowTest φ f 1) : E → ℂ) ξ =
    𝓕 (windowTest (derivativeWindow b φ) f 1 : E → ℂ) ξ
  rw [coordinateDerivative, fourier_pderiv, windowTest_fourier, windowTest_fourier,
    one_smul, derivativeWindow_apply]
  ring

/-- A fixed Schwartz frequency window and its differentiated output are
bounded on the original field's finite-exponent space. -/
theorem exists_fixedWindow_coordinateDerivative_Lp_bound
    (b : Fin 4) (φ : SchwartzMap E ℂ) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      eLpNorm (coordinateDerivative b (windowTest φ f 1) : E → ℂ) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  let ψ := derivativeWindow b φ
  obtain ⟨K, hK, hWindow⟩ := maximalShiftedWindow_Lp ψ
  let C := K * maximalConstant p ^ (1 / p)
  have hC : C < ⊤ := ENNReal.mul_lt_top hK
    (ENNReal.rpow_lt_top_of_nonneg (by positivity) (maximalConstant_finite p).ne)
  refine ⟨C, hC, fun f => ?_⟩
  rw [coordinateDerivative_windowTest_one]
  have pointwise (x : E) : ‖windowTest ψ f 1 x‖ₑ ≤ maximalShiftedWindow ψ f 0 x := by
    have eq := windowTest_translate ψ f 1 1 one_pos x (0 : E)
    simp only [smul_zero, sub_zero] at eq
    rw [eq]
    exact le_iSup_of_le ⟨1, one_pos⟩ le_rfl
  calc
    _ ≤ eLpNorm (maximalShiftedWindow ψ f 0) (ENNReal.ofReal p) volume :=
      eLpNorm_mono_enorm (fun x => by simpa only [enorm_eq_self] using pointwise x)
    _ ≤ _ := by simpa [C] using hWindow f (0 : E) p hp

/-- Fixed bounded-frequency terms vanish after one derivative when the
undifferentiated original fields tend to zero in finite-exponent norm. -/
theorem tendsto_fixedWindow_coordinateDerivative_Lp_zero
    (b : Fin 4) (φ : SchwartzMap E ℂ) (p : ℝ) (hp : 1 < p) (f : ℕ → SchwartzMap E ℂ)
    (hf : Tendsto (fun n => (eLpNorm (f n : E → ℂ) (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (eLpNorm (coordinateDerivative b (windowTest φ (f n) 1) : E → ℂ) (ENNReal.ofReal p) volume).toReal)
      atTop (𝓝 0) := by
  obtain ⟨C, hC, h⟩ := exists_fixedWindow_coordinateDerivative_Lp_bound b φ p hp
  have hUpper : Tendsto (fun n => C.toReal * (eLpNorm (f n : E → ℂ) (ENNReal.ofReal p) volume).toReal)
      atTop (𝓝 0) := by simpa only [mul_zero] using hf.const_mul C.toReal
  refine squeeze_zero (fun _ => ENNReal.toReal_nonneg) (fun n => ?_) hUpper
  have hFinite : C * eLpNorm (f n : E → ℂ) (ENNReal.ofReal p) volume < ⊤ :=
    ENNReal.mul_lt_top hC ((f n).memLp (ENNReal.ofReal p) volume).eLpNorm_lt_top
  exact (ENNReal.toReal_mono hFinite.ne (h (f n))).trans_eq ENNReal.toReal_mul

/-- Comparing two fixed frequency windows keeps the original field in
both slots. The difference is again a single Schwartz window. -/
theorem tendsto_fixedWindows_difference_coordinateDerivative_Lp_zero
    (b : Fin 4) (φ ψ : SchwartzMap E ℂ) (p : ℝ) (hp : 1 < p) (f : ℕ → SchwartzMap E ℂ)
    (hf : Tendsto (fun n => (eLpNorm (f n : E → ℂ) (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (eLpNorm (coordinateDerivative b (windowTest φ (f n) 1 - windowTest ψ (f n) 1) : E → ℂ)
        (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
  have difference (g : SchwartzMap E ℂ) : windowTest (φ - ψ) g 1 = windowTest φ g 1 - windowTest ψ g 1 := by
    apply (SchwartzMap.fourierTransformCLE ℂ).injective
    rw [map_sub]
    ext ξ
    change 𝓕 (windowTest (φ - ψ) g 1 : E → ℂ) ξ =
      𝓕 (windowTest φ g 1 : E → ℂ) ξ - 𝓕 (windowTest ψ g 1 : E → ℂ) ξ
    simp only [windowTest_fourier, one_smul, SchwartzMap.sub_apply, mul_sub]
  simpa only [difference] using tendsto_fixedWindow_coordinateDerivative_Lp_zero b (φ - ψ) p hp f hf

/-- The original high-pass convention has exactly this vanishing derivative
remainder on the same field. -/
theorem tendsto_projectionInfrared_coordinateDerivative_remainder_Lp_zero
    (b : Fin 4) (p : ℝ) (hp : 1 < p) (f : ℕ → SchwartzMap E ℂ)
    (hf : Tendsto (fun n => (eLpNorm (f n : E → ℂ) (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (eLpNorm (coordinateDerivative b (f n - projectionInfraredAction (f n)) : E → ℂ)
        (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
  let φ := lowInfraredSchwartz gaugeProjectionInfrared gaugeProjectionInfrared_contDiff
    1 2 zero_lt_one (fun _ hs => gaugeProjectionInfrared_zero hs) (fun _ hs => gaugeProjectionInfrared_one hs)
  have eq (n : ℕ) : f n - projectionInfraredAction (f n) = windowTest φ (f n) 1 := by
    change f n - (f n - windowTest φ (f n) 1) = _
    exact sub_sub_cancel _ _
  simpa only [eq] using tendsto_fixedWindow_coordinateDerivative_Lp_zero b φ p hp f hf

end Burnett.C02
