import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadialProfile

set_option autoImplicit false
set_option maxHeartbeats 3100000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open scoped FourierTransform ContDiff

/-- One annular window sufficient for all the input and output plateaus of
the narrow reference family, including the low-coefficient margins. -/
theorem exists_narrowReference_annulus :
    ∃ q : SchwartzMap E ℂ, HasCompactSupport (q : E → ℂ) ∧
      (∀ z, q z≠0 → 1/2<‖z‖ ∧ ‖z‖<2) ∧
      ∀ z, (65/128 : ℝ)≤‖z‖ → ‖z‖≤127/64 → q z=1 := by
  obtain ⟨outer,houter,outerOne,outerZero,_⟩ := exists_coefficientRadialProfile (127/64) 2 (by norm_num) (by norm_num)
  obtain ⟨inner,_,innerOne,innerZero,_⟩ := exists_coefficientRadialProfile (1/2) (65/128) (by norm_num) (by norm_num)
  let Q (z : E) := outer z*(1-inner z)
  have hc : HasCompactSupport Q :=
    houter.of_isClosed_subset isClosed_closure (closure_mono fun z hz => by
      by_contra h
      change ¬ outer z ≠ 0 at h
      have h0 := not_ne_iff.mp h
      exact hz (by simp only [Q,h0,zero_mul]))
  have hs : ContDiff ℝ ∞ Q := outer.smooth'.mul (contDiff_const.sub inner.smooth')
  let q := hc.toSchwartzMap hs
  refine ⟨q,hc,?_,?_⟩
  · intro z hz
    constructor
    · by_contra! hn
      exact hz (show Q z=0 by simp only [Q,innerOne _ hn,sub_self,mul_zero])
    · by_contra! hn
      exact hz (show Q z=0 by simp only [Q,outerZero _ hn,zero_mul])
  · intro z h₁ h₂
    change Q z=1
    simp only [Q,outerOne _ h₂,innerZero _ h₁,sub_zero,mul_one]

private def narrowLowCoefficientDilation : E ≃L[ℝ] E :=
  (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) (128:ℝ) (by norm_num)).toContinuousLinearEquiv

def narrowLowCoefficientProfile (χ : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ narrowLowCoefficientDilation χ

theorem narrowLowCoefficientProfile_apply (χ : SchwartzMap E ℂ) (z : E) :
    narrowLowCoefficientProfile χ z = χ ((128:ℝ) • z) := rfl

theorem narrowLowCoefficientProfile_support (χ : SchwartzMap E ℂ)
    (hχ : ∀ z : E, (7/4 : ℝ)≤‖z‖ → χ z=0) :
    ∀ z, narrowLowCoefficientProfile χ z≠0 → ‖z‖≤(7/512 : ℝ) := by
  intro z hz
  by_contra! h
  apply hz
  rw [narrowLowCoefficientProfile_apply]
  apply hχ
  rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤128)]
  linarith only [h]

theorem narrowLowCoefficientProfile_window (χ D : SchwartzMap E ℂ) (s : ℝ) :
    windowTest (narrowLowCoefficientProfile χ) D s = windowTest χ D (128*s) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext z
  change 𝓕 (windowTest (narrowLowCoefficientProfile χ) D s : E → ℂ) z =
    𝓕 (windowTest χ D (128*s) : E → ℂ) z
  simp only [windowTest_fourier,narrowLowCoefficientProfile_apply,smul_smul]

theorem narrowDyadicBandpass_support (χ : SchwartzMap E ℂ)
    (h₁ : ∀ z : E, ‖z‖≤(5/4 : ℝ) → χ z=1) (h₀ : ∀ z : E, (7/4 : ℝ)≤‖z‖ → χ z=0) :
    ∀ z, coefficientDyadicBandpass χ z≠0 → (5/8 : ℝ)≤‖z‖ ∧ ‖z‖≤7/4 := by
  intro z hz
  have norm_double : ‖(2:ℝ) • z‖ = 2*‖z‖ := by rw [norm_smul]; norm_num
  rw [coefficientDyadicBandpass_apply] at hz
  constructor
  · by_contra! h
    apply hz
    rw [h₁ _ (by linarith),h₁ _ (by rw [norm_double]; linarith),sub_self]
  · by_contra! h
    apply hz
    rw [h₀ _ (by linarith),h₀ _ (by rw [norm_double]; linarith),sub_self]

end Burnett.A06
