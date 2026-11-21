import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyKernel
import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyCommutator

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform

private theorem weighted_integrand_integrable {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (w : E → ℂ) (hw : Continuous w) (hb : ∀ ξ, ‖w ξ‖ ≤ 1) (f : SchwartzMap E ℂ) (x : E) :
    Integrable (fun ξ => (Real.fourierChar (inner ℝ ξ x)) •
      ((w ξ * a x ξ) * (𝓕 (f : E → ℂ)) ξ)) := by
  obtain ⟨D,hD,hGrowth⟩ := ha.order 0
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have hI : Integrable (fun ξ : E => D*((1+‖ξ‖)*‖F ξ‖)) := by
    simpa only [add_mul,one_mul,pow_one] using
      (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)).const_mul D
  have hPhase : Continuous (fun ξ : E => Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  refine hI.mono' (hPhase.smul ((hw.mul (ha.smooth x).continuous).mul F.continuous)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => ?_)
  rw [Circle.norm_smul]
  change ‖(w ξ * a x ξ) * F ξ‖ ≤ D*((1+‖ξ‖)*‖F ξ‖)
  rw [norm_mul,norm_mul]
  have hD' : ‖a x ξ‖ ≤ D*(1+‖ξ‖) := by
    simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hGrowth x ξ
  exact (mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hb ξ)).trans hD') (norm_nonneg _)).trans_eq (by ring)

/-- The whole original symbol splits into the actual low and high operators
on the same Schwartz test for the one fixed infrared cutoff. -/
theorem firstOrderAction_eq_low_add_high {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (f : SchwartzMap E ℂ) (x : E) :
    firstOrderAction a f x = firstOrderLowAction a f x + firstOrderHighAction a f x := by
  let w₀ (ξ : E) : ℂ := (radialCore ξ : ℂ)
  let w₁ (ξ : E) : ℂ := ((1-radialCore ξ : ℝ) : ℂ)
  have h₀ : ∀ ξ, ‖w₀ ξ‖ ≤ 1 := fun ξ => by
    rw [show w₀ ξ = (radialCore ξ : ℂ) from rfl,Complex.norm_real,
      Real.norm_of_nonneg (radialCore_nonneg ξ)]
    exact radialCore_le_one ξ
  have h₁ : ∀ ξ, ‖w₁ ξ‖ ≤ 1 := fun ξ => by
    rw [show w₁ ξ = ((1-radialCore ξ : ℝ) : ℂ) from rfl,Complex.norm_real,
      Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ξ))]
    linarith only [radialCore_nonneg ξ]
  have hw₀ : Continuous w₀ := Complex.continuous_ofReal.comp radialCore_contDiff.continuous
  have hw₁ : Continuous w₁ := Complex.continuous_ofReal.comp
    (continuous_const.sub radialCore_contDiff.continuous)
  unfold firstOrderLowAction firstOrderAction firstOrderHighAction
  simp only [Real.fourierIntegralInv_eq]
  change (∫ ξ, (Real.fourierChar (inner ℝ ξ x)) • (a x ξ * (𝓕 (f : E → ℂ)) ξ)) =
    (∫ ξ, (Real.fourierChar (inner ℝ ξ x)) • ((w₀ ξ*a x ξ)*(𝓕 (f : E → ℂ)) ξ)) +
      ∫ ξ, (Real.fourierChar (inner ℝ ξ x)) • ((w₁ ξ*a x ξ)*(𝓕 (f : E → ℂ)) ξ)
  rw [← integral_add (weighted_integrand_integrable ha w₀ hw₀ h₀ f x)
    (weighted_integrand_integrable ha w₁ hw₁ h₁ f x)]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [← smul_add]
  congr 1
  simp only [w₀,w₁,Complex.ofReal_sub,Complex.ofReal_one]
  ring

/-- The two frequency branches use exactly the same pointwise coefficient
product in the actual commutator, without changing the spatial test. -/
theorem full_coefficient_commutator_split {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (r f rf : SchwartzMap E ℂ) (hrf : ∀ y, rf y = r y*f y) (x : E) :
    r x*firstOrderAction a f x - firstOrderAction a rf x =
      lowCoefficientCommutator a r f x +
        (r x*firstOrderHighAction a f x - firstOrderHighAction a rf x) := by
  rw [firstOrderAction_eq_low_add_high ha f x,firstOrderAction_eq_low_add_high ha rf x]
  unfold lowCoefficientCommutator
  rw [← show (rf : E → ℂ) = fun y => r y*f y from funext hrf]
  ring

end Burnett.Analysis.FirstOrderDyadic
