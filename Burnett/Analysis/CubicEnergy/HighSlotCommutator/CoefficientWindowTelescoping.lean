import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Filter Finset
open scoped FourierTransform Topology BigOperators

private def coefficientDouble : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) 2 (by norm_num)).toContinuousLinearEquiv

private def coefficientDoubleWindow (χ : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coefficientDouble χ

/-- The exact difference of two fixed dilations of the same low-pass profile. -/
def coefficientDyadicBandpass (χ : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  χ - coefficientDoubleWindow χ

theorem coefficientDyadicBandpass_apply (χ : SchwartzMap E ℂ) (x : E) :
    coefficientDyadicBandpass χ x = χ x - χ ((2:ℝ) • x) := rfl

theorem coefficientDyadicBandpass_compact (χ : SchwartzMap E ℂ)
    (hc : HasCompactSupport (χ : E → ℂ)) :
    HasCompactSupport (coefficientDyadicBandpass χ : E → ℂ) := by
  change HasCompactSupport (fun x : E => χ x - χ (coefficientDouble x))
  exact hc.sub (hc.comp_homeomorph coefficientDouble.toHomeomorph)

/-- A low-pass equal to one slightly beyond radius one and zero strictly
before radius two supplies the same strict annulus used in the square bounds. -/
theorem coefficientDyadicBandpass_annulus (χ : SchwartzMap E ℂ) {a b : ℝ}
    (ha : 1<a) (hb : b<2)
    (hχ₁ : ∀ x : E, ‖x‖ ≤ a → χ x=1) (hχ₀ : ∀ x : E, b ≤ ‖x‖ → χ x=0) :
    ∀ x : E, coefficientDyadicBandpass χ x ≠ 0 → 1/2 < ‖x‖ ∧ ‖x‖ < 2 := by
  intro x hx
  have norm_double : ‖(2:ℝ) • x‖ = 2*‖x‖ := by rw [norm_smul]; norm_num
  constructor
  · by_contra! h
    apply hx
    rw [coefficientDyadicBandpass_apply,hχ₁ _ (by linarith),hχ₁ _ (by rw [norm_double]; linarith),sub_self]
  · by_contra! h
    apply hx
    rw [coefficientDyadicBandpass_apply,hχ₀ _ (by linarith),hχ₀ _ (by rw [norm_double]; linarith),sub_self]

private theorem windowTest_dyadicBandpass (χ D : SchwartzMap E ℂ) (S : ℝ) :
    windowTest (coefficientDyadicBandpass χ) D S =
      windowTest χ D S - windowTest χ D (2*S) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext z
  change (SchwartzMap.fourierTransformCLM ℂ _) z = (SchwartzMap.fourierTransformCLM ℂ _) z
  rw [map_sub]
  simp only [SchwartzMap.sub_apply,SchwartzMap.fourierTransformCLM_apply,windowTest_fourier,
    coefficientDyadicBandpass_apply,smul_smul,mul_sub]

/-- Relative physical scale of the coefficient band. Its frequency grows
as the nonnegative integer index grows. -/
def dyadicCoefficientScale (S : ℝ) (j : ℕ) : ℝ := S/(2:ℝ)^j

theorem dyadicCoefficientScale_pos {S : ℝ} (hS : 0<S) (j : ℕ) : 0<dyadicCoefficientScale S j := by
  unfold dyadicCoefficientScale
  positivity

theorem dyadicCoefficientScale_succ (S : ℝ) (j : ℕ) :
    2*dyadicCoefficientScale S (j+1) = dyadicCoefficientScale S j := by
  unfold dyadicCoefficientScale
  rw [pow_succ]
  field_simp

theorem dyadicCoefficientScale_tendsto_zero (S : ℝ) :
    Tendsto (dyadicCoefficientScale S) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤1/2)
    (by norm_num : (1:ℝ)/2<1)).const_mul S
  simpa only [dyadicCoefficientScale,one_div,inv_pow,div_eq_mul_inv,mul_zero,one_mul] using h

/-- The finite coefficient decomposition is an equality of actual Schwartz
Fourier windows. The low-pass scale and the first retained annulus share
the same initial scale, with no unspecified remainder. -/
theorem windowTest_coefficient_telescoping (χ D : SchwartzMap E ℂ) (S : ℝ) (N : ℕ) :
    windowTest χ D S +
      (∑ j ∈ range N, windowTest (coefficientDyadicBandpass χ) D (dyadicCoefficientScale S (j+1))) =
    windowTest χ D (dyadicCoefficientScale S N) := by
  induction N with
  | zero => simp [dyadicCoefficientScale]
  | succ n ih =>
    rw [sum_range_succ,← add_assoc,ih,windowTest_dyadicBandpass,dyadicCoefficientScale_succ]
    abel

end Burnett.A06
