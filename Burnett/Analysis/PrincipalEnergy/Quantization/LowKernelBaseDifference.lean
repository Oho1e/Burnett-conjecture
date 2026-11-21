import Burnett.Analysis.PrincipalEnergy.Quantization.FixedLowInverseProfiles

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Bornology Filter Set MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform InnerProduct

private def baseDifferenceQuotient (a : E → E → ℂ) (p : E × E) (ξ : E) : ℂ :=
  ‖p.1-p.2‖⁻¹ • (a p.1 ξ-a p.2 ξ)

private theorem baseDifferenceQuotient_low_order {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ p ξ, ‖ξ‖≤2 →
      ‖iteratedFDeriv ℝ n (baseDifferenceQuotient a p) ξ‖≤C := by
  obtain ⟨C,hC,hBound⟩ := exists_frequencyDerivative_baseDifference_bound ha n
  refine ⟨3*C,mul_nonneg (by norm_num) hC,?_⟩
  rintro ⟨x,y⟩ ξ hξ
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hx : ContDiffAt ℝ n (a x) ξ := (ha.frequency.smooth x).contDiffAt.of_le hn
  have hy : ContDiffAt ℝ n (a y) ξ := (ha.frequency.smooth y).contDiffAt.of_le hn
  have hNeg : ContDiffAt ℝ n (-(a y)) ξ := hy.neg
  have hAdd : ContDiffAt ℝ n (a x+ -(a y)) ξ := hx.add hNeg
  change ‖iteratedFDeriv ℝ n (‖x-y‖⁻¹ • (a x + -(a y))) ξ‖≤_
  rw [iteratedFDeriv_const_smul_apply hAdd,iteratedFDeriv_add_apply hx hNeg,
    iteratedFDeriv_neg_apply,← sub_eq_add_neg,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
  have hW : 1≤(1+‖ξ‖)^n := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  have hRel : ‖iteratedFDeriv ℝ n (a x) ξ-iteratedFDeriv ℝ n (a y) ξ‖≤C*‖x-y‖*(1+‖ξ‖) :=
    (le_mul_of_one_le_right (norm_nonneg _) hW).trans (hBound x y ξ)
  by_cases hZero : ‖x-y‖=0
  · rw [hZero,inv_zero,zero_mul]
    exact mul_nonneg (by norm_num) hC
  calc
    _ ≤ ‖x-y‖⁻¹*(C*‖x-y‖*(1+‖ξ‖)) := mul_le_mul_of_nonneg_left hRel (inv_nonneg.mpr (norm_nonneg _))
    _ = C*(1+‖ξ‖) := by field_simp [hZero]
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (by linarith : 1+‖ξ‖≤3) hC
      linarith

private theorem inverseFourier_real_smul_sub (f g : E → ℂ) (hf : Integrable f volume)
    (hg : Integrable g volume) (c : ℝ) (z : E) :
    (𝓕⁻ (c • (f-g))) z = c • ((𝓕⁻ f) z-(𝓕⁻ g) z) := by
  simp only [Real.fourierIntegralInv_eq,Pi.smul_apply,Pi.sub_apply]
  let h (ξ : E) := Real.fourierChar (inner ℝ ξ z)
  have hEq : (fun ξ : E => h ξ • (c • (f ξ-g ξ))) =
      fun ξ : E => c • (h ξ • f ξ-h ξ • g ξ) := by
    funext ξ
    rw [smul_comm (h ξ) c,smul_sub (h ξ)]
  change (∫ ξ, h ξ • (c • (f ξ-g ξ))) =
    c • ((∫ ξ, h ξ • f ξ)-(∫ ξ, h ξ • g ξ))
  rw [hEq,integral_smul]
  have hh : Continuous h := Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  have hInt {w : E → ℂ} (hw : Integrable w volume) : Integrable (fun ξ => h ξ • w ξ) volume :=
    hw.mono (hh.aestronglyMeasurable.smul hw.1) (Eventually.of_forall fun ξ => by rw [Circle.norm_smul])
  rw [integral_sub (hInt hf) (hInt hg)]

/-- Changing only the base of the true fixed-cutoff low kernel costs the
base-point distance and preserves the inverse sixth-power spatial bound. -/
theorem exists_firstOrderLowKernel_baseDifference {a : E → E → ℂ} (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0≤C ∧ ∀ x y z, z≠0 →
      ‖firstOrderLowKernel a x z-firstOrderLowKernel a y z‖≤C*‖x-y‖*(‖z‖^6)⁻¹ := by
  obtain ⟨p,hp,hP⟩ := exists_fixedLowInverseProfiles (baseDifferenceQuotient a)
    (fun q => ((ha.frequency.smooth q.1).sub (ha.frequency.smooth q.2)).const_smul _)
    (baseDifferenceQuotient_low_order ha)
  rw [← image_univ] at hP
  have hProfile := ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded p).mp hP
  obtain ⟨C,hC,hBound⟩ := hProfile (6,0)
  refine ⟨C,hC.le,?_⟩
  intro x y z hz
  by_cases hxy : x=y
  · simp [hxy]
  have hd : ‖x-y‖≠0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  have hInput :
      (fun ξ => (radialCore ξ : ℂ)*baseDifferenceQuotient a (x,y) ξ) =
        ‖x-y‖⁻¹ • (firstOrderLowSymbol a x-firstOrderLowSymbol a y) := by
    funext ξ
    change (radialCore ξ : ℂ) • (‖x-y‖⁻¹ • (a x ξ-a y ξ)) =
      ‖x-y‖⁻¹ • ((radialCore ξ : ℂ) • a x ξ-(radialCore ξ : ℂ) • a y ξ)
    rw [smul_comm (radialCore ξ : ℂ) (‖x-y‖⁻¹),smul_sub (radialCore ξ : ℂ)]
  have hValue : p (x,y) z =
      ‖x-y‖⁻¹ • (firstOrderLowKernel a x z-firstOrderLowKernel a y z) := by
    rw [show p (x,y) z=(𝓕⁻ (fun ξ => (radialCore ξ : ℂ)*baseDifferenceQuotient a (x,y) ξ)) z
      from congrFun (hp (x,y)) z,hInput,
      inverseFourier_real_smul_sub _ _ (firstOrderLowSymbol_integrable ha.frequency x)
        (firstOrderLowSymbol_integrable ha.frequency y)]
    rfl
  have hPSize : ‖p (x,y) z‖≤C*(‖z‖^6)⁻¹ := by
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hz) _)).mpr
    rw [mul_comm]
    exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ (p (x,y)) 6 z).trans (hBound (x,y) trivial).le
  calc
    _ = ‖‖x-y‖ • p (x,y) z‖ := by rw [hValue,smul_smul,mul_inv_cancel₀ hd,one_smul]
    _ = ‖x-y‖*‖p (x,y) z‖ := by rw [norm_smul,Real.norm_of_nonneg (norm_nonneg _)]
    _ ≤ ‖x-y‖*(C*(‖z‖^6)⁻¹) := mul_le_mul_of_nonneg_left hPSize (norm_nonneg _)
    _ = _ := by ring

end Burnett.Analysis.FirstOrderDyadic
