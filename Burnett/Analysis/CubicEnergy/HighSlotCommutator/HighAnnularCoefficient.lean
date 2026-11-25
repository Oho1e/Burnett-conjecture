import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLowCoefficientInputs

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section
namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open scoped FourierTransform ComplexConjugate NNReal

private def gapInverseProfile (a : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm a

/-- First absolute physical moment of the fixed coefficient window. -/
def coefficientBandpassMoment (a : SchwartzMap E ℂ) : ℝ≥0 :=
  (∫ z : E, ‖z‖*‖gapInverseProfile a z‖).toNNReal

private theorem inverseProfile_mean_zero (a : SchwartzMap E ℂ) (ha : a 0 = 0) :
    (∫ z : E, gapInverseProfile a z) = 0 := by
  have h : 𝓕 (gapInverseProfile a : E → ℂ) 0 = a 0 := by
    change (SchwartzMap.fourierTransformCLE ℂ (gapInverseProfile a)) 0 = _
    rw [gapInverseProfile,ContinuousLinearEquiv.apply_symm_apply]
  rw [Real.fourierIntegral_eq'] at h
  simpa only [inner_zero_right,mul_zero,Complex.ofReal_zero,zero_mul,Complex.exp_zero,
    one_smul,ha] using h

private theorem coefficientWindow_convolution (a D : SchwartzMap E ℂ)
    {s : ℝ} (hs : 0 < s) (x : E) :
    windowTest a D s x = ∫ z : E, gapInverseProfile a z * D (x-s • z) := by
  let K := fun z : E => gapInverseProfile a z * D (x-s • z)
  have loc := windowTest_translate a D s 0 hs x (0 : E)
  simp only [smul_zero,sub_zero] at loc
  rw [loc,shifted_window_physical a D s hs]
  have formula (y : E) :
      ((s^4)⁻¹ • ((SchwartzMap.fourierTransformCLE ℂ).symm a) (s⁻¹ • (x-y)+0)) * D y =
        (s^4)⁻¹ • K (s⁻¹ • (x-y)) := by
    unfold K gapInverseProfile
    rw [add_zero,smul_smul,mul_inv_cancel₀ hs.ne',one_smul,sub_sub_cancel,smul_mul_assoc]
  simp_rw [formula]
  let Q := fun z : E => (s^4)⁻¹ • K (s⁻¹ • z)
  change (∫ y : E, Q (x-y)) = _
  have hm := (volume : Measure E).measurePreserving_sub_left x
  rw [hm.integral_comp (Homeomorph.subLeft x).measurableEmbedding Q]
  unfold Q
  rw [integral_smul,Measure.integral_comp_inv_smul_of_nonneg volume K hs.le,
    show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin,smul_smul,
    inv_mul_cancel₀ (pow_ne_zero _ hs.ne'),one_smul]

/-- Cancellation of one actual Fourier annulus gives the factor of its
physical scale in the uniform bound on a Lipschitz coefficient. -/
theorem coefficientWindow_norm_le_scale (a D : SchwartzMap E ℂ) (hzero : a 0 = 0)
    {L : ℝ≥0} (hD : LipschitzWith L D) {s : ℝ} (hs : 0 < s) (x : E) :
    ‖windowTest a D s x‖ ≤ ((coefficientBandpassMoment a*L : ℝ≥0) : ℝ)*s := by
  let φ := gapInverseProfile a
  have φ0 : (∫ z : E, φ z) = 0 := inverseProfile_mean_zero a hzero
  have hB : (coefficientBandpassMoment a : ℝ) = ∫ z : E, ‖z‖*‖φ z‖ :=
    Real.coe_toNNReal _ (integral_nonneg (fun _ => by positivity))
  have hshift : Continuous (fun z : E => D (x-s • z)) :=
    D.continuous.comp (continuous_const.sub (continuous_const.smul continuous_id))
  have hmain : Integrable (fun z : E => φ z * D (x-s • z)) := by
    refine (φ.integrable.norm.mul_const (SchwartzMap.seminorm ℝ 0 0 D)).mono'
      (φ.continuous.mul hshift).aestronglyMeasurable ?_
    filter_upwards with z
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (D.norm_le_seminorm ℝ _) (norm_nonneg _)
  have const0 : (∫ z : E, φ z * D x) = 0 := by
    rw [integral_mul_const,φ0,zero_mul]
  have moment : Integrable (fun z : E => ‖z‖*‖φ z‖) := by
    simpa only [pow_one] using φ.integrable_pow_mul (volume : Measure E) 1
  have hdiff (z : E) : ‖D (x-s • z) - D x‖ ≤ (L : ℝ)*s*‖z‖ := by
    have h := hD.dist_le_mul (x-s • z) x
    rw [dist_eq_norm,dist_eq_norm,show x-s • z-x = -(s • z) by abel,norm_neg,norm_smul,
      Real.norm_of_nonneg hs.le] at h
    simpa only [mul_assoc] using h
  have eq : windowTest a D s x =
      ∫ z : E, (φ z * D (x-s • z) - φ z * D x) := by
    rw [coefficientWindow_convolution a D hs, integral_sub hmain (φ.integrable.mul_const (D x)),
      const0,sub_zero]
  rw [eq]
  calc
    _ ≤ ∫ z : E, ‖φ z * D (x-s • z) - φ z * D x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ z : E, (‖z‖*‖φ z‖)*((L : ℝ)*s) := by
      refine integral_mono (hmain.sub (φ.integrable.mul_const _)).norm (moment.mul_const _) fun z => ?_
      rw [← mul_sub,norm_mul]
      exact (mul_le_mul_of_nonneg_left (hdiff z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := by rw [integral_mul_const,NNReal.coe_mul,hB]; ring

def gapConjugate (D : SchwartzMap E ℂ) : SchwartzMap E ℂ where
  toFun := Complex.conjLIE ∘ (D : E → ℂ)
  smooth' := Complex.conjCLE.contDiff.comp D.smooth'
  decay' k n := by
    obtain ⟨C, _, hC⟩ := D.decay k n
    refine ⟨C, fun x => ?_⟩
    rw [Complex.conjLIE.norm_iteratedFDeriv_comp_left]
    exact hC x

theorem gapConjugate_fourier (D : SchwartzMap E ℂ) (z : E) :
    𝓕 (gapConjugate D : E → ℂ) z = conj (𝓕 (D : E → ℂ) (-z)) := by
  rw [← radianFourier_scaled,← radianFourier_scaled,smul_neg]
  change radianFourier (fun x => conj (D x)) (tau • z) = _
  simpa only [neg_neg] using (radianFourier_conj_neg D (-(tau • z)))

/-- An actual annular cutoff of the coefficient, made real, is Schwartz and
has the same annular support together with the mean-zero amplitude estimate. -/
theorem exists_actual_spectralAnnularCoefficient
    (a D : SchwartzMap E ℂ) {lo hi : ℝ} (hlo : 0 < lo)
    (ha : ∀ z : E, a z ≠ 0 → lo ≤ ‖z‖ ∧ ‖z‖ ≤ hi)
    {L : ℝ≥0} (hD : LipschitzWith L D) {s : ℝ} (hs : 0 < s) :
    ∃ C : SchwartzMap E ℂ,
      (∀ x, C x = ((windowTest a D s x).re : ℂ)) ∧
      (∀ x, ‖C x‖ ≤ ((coefficientBandpassMoment a*L : ℝ≥0) : ℝ)*s) ∧
      ∀ z : E, 𝓕 (C : E → ℂ) z ≠ 0 → lo ≤ ‖s • z‖ ∧ ‖s • z‖ ≤ hi := by
  let U := windowTest a D s
  let C := (2⁻¹ : ℂ) • (U + gapConjugate U)
  have hReal (x : E) : C x = ((U x).re : ℂ) := by
    change (2⁻¹ : ℂ) * (U x + conj (U x)) = ((U x).re : ℂ)
    have half : (2⁻¹ : ℂ) = ((1/2 : ℝ) : ℂ) := by norm_num
    rw [half]
    apply Complex.ext
    · simp [Complex.mul_re,Complex.add_re]
      ring
    · simp [Complex.mul_im,Complex.add_im]
  have hzero : a 0 = 0 := by
    by_contra hne
    have h := (ha 0 hne).1
    rw [norm_zero] at h
    exact (not_le_of_gt hlo) h
  refine ⟨C,hReal,fun x => ?_,?_⟩
  · rw [hReal,Complex.norm_real,Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans (coefficientWindow_norm_le_scale a D hzero hD hs x)
  · intro z hz
    by_contra h
    have z0 : a (s • z) = 0 := by
      by_contra hz'
      exact h (ha _ hz')
    have neg0 : a (s • (-z)) = 0 := by
      by_contra hz'
      exact h (by simpa only [smul_neg,norm_neg] using ha _ hz')
    apply hz
    change (SchwartzMap.fourierTransformCLM ℂ C) z = 0
    unfold C
    rw [map_smul,map_add]
    simp only [SchwartzMap.smul_apply,SchwartzMap.add_apply,SchwartzMap.fourierTransformCLM_apply,
      gapConjugate_fourier,U,windowTest_fourier,z0,neg0,mul_zero,map_zero,add_zero,smul_zero]

end Burnett.A06
