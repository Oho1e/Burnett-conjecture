import Burnett.Analysis.PrincipalEnergy.Quantization.NormalizedBaseIdentification
import Burnett.Analysis.PrincipalEnergy.Fourier.FrequencyWeights

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Fourier Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.HminusReverse Burnett.Analysis.HminusWeightedDual
open scoped FourierTransform

/-- The first-order weight reinstates exactly the normalized base symbol. -/
def firstOrderWeightedFourier (f : SchwartzMap E ℂ) (ξ : E) : ℂ :=
  (1 + ‖ξ‖) • (𝓕 (f : E → ℂ)) ξ

theorem firstOrderWeightedFourier_continuous (f : SchwartzMap E ℂ) :
    Continuous (firstOrderWeightedFourier f) :=
  (continuous_const.add continuous_norm).smul (SchwartzMap.fourierTransformCLM ℂ f).continuous

theorem firstOrderWeightedFourier_integrable (f : SchwartzMap E ℂ) :
    Integrable (firstOrderWeightedFourier f) := by
  let G := SchwartzMap.fourierTransformCLM ℂ f
  apply (G.integrable.norm.add (G.integrable_pow_mul (volume : Measure E) 1)).mono'
    (firstOrderWeightedFourier_continuous f).aestronglyMeasurable
  filter_upwards with ξ
  rw [firstOrderWeightedFourier, norm_smul, Real.norm_of_nonneg (by positivity)]
  simp only [Pi.add_apply, pow_one]
  change (1 + ‖ξ‖) * ‖G ξ‖ ≤ ‖G ξ‖ + ‖ξ‖ * ‖G ξ‖
  nlinarith

private theorem integrable_schwartz_square_moment (G : SchwartzMap E ℂ) :
    Integrable (fun ξ : E => (1 + ‖ξ‖)^2 * ‖G ξ‖^2) := by
  let M := SchwartzMap.seminorm ℂ 0 0 G
  have hm (ξ : E) : ‖G ξ‖ ≤ M := SchwartzMap.norm_le_seminorm ℂ G ξ
  have hg : Integrable (fun ξ : E => (1 + ‖ξ‖)^2 * ‖G ξ‖) := by
    have hi := (G.integrable.norm.add ((G.integrable_pow_mul (volume : Measure E) 1).const_mul 2)).add
      (G.integrable_pow_mul (volume : Measure E) 2)
    refine hi.congr (Eventually.of_forall fun ξ => ?_)
    simp only [Pi.add_apply, pow_one]
    ring
  exact (hg.const_mul M).mono'
    (((continuous_const.add continuous_norm).pow 2).mul (G.continuous.norm.pow 2)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (by positivity)]
      calc
        _ ≤ (1 + ‖ξ‖)^2 * (M * ‖G ξ‖) := by
          rw [pow_two ‖G ξ‖]
          gcongr
          exact hm ξ
        _ = _ := by ring)

theorem firstOrderWeightedFourier_memLp (f : SchwartzMap E ℂ) :
    MemLp (firstOrderWeightedFourier f) 2 (volume : Measure E) := by
  apply (memLp_two_iff_integrable_sq_norm (firstOrderWeightedFourier_continuous f).aestronglyMeasurable).mpr
  apply (integrable_schwartz_square_moment (SchwartzMap.fourierTransformCLM ℂ f)).congr
  filter_upwards with ξ
  rw [firstOrderWeightedFourier, norm_smul, mul_pow, Real.norm_of_nonneg (by positivity)]
  rfl

/-- The actual squared norm of the weighted Fourier input is bounded by twice
the coordinate H¹ energy of the same Schwartz input. -/
theorem firstOrderWeightedFourier_h1_bound (f : SchwartzMap E ℂ) :
    ‖(firstOrderWeightedFourier_memLp f).toLp (firstOrderWeightedFourier f)‖^2 ≤
      2 * schwartzH1Energy f := by
  rw [schwartzH1Energy_eq_fourierH1Energy, l2_norm_sq_integral, fourierH1Energy]
  have hEq := MemLp.coeFn_toLp (firstOrderWeightedFourier_memLp f)
  have hIn (ξ : E) :
      ‖firstOrderWeightedFourier f ξ‖^2 = (1 + ‖ξ‖)^2 * ‖(𝓕 (f : E → ℂ)) ξ‖^2 := by
    rw [firstOrderWeightedFourier, norm_smul, Real.norm_of_nonneg (by positivity), mul_pow]
  rw [integral_congr_ae (hEq.mono fun ξ h => by rw [h,hIn]), ← integral_const_mul]
  let G := SchwartzMap.fourierTransformCLM ℂ f
  have hInt := integrable_schwartz_square_moment G
  have hUpper : Integrable (fun ξ : E => 2 * (frequencyWeight ξ * ‖G ξ‖^2)) := by
    refine (hInt.const_mul (2 * (1 + 4 * Real.pi^2))).mono'
      (continuous_const.mul (frequencyWeight_continuous.mul (G.continuous.norm.pow 2))).aestronglyMeasurable ?_
    filter_upwards with ξ
    rw [Real.norm_of_nonneg (mul_nonneg (by norm_num)
      (mul_nonneg (frequencyWeight_pos ξ).le (sq_nonneg _)))]
    have h : frequencyWeight ξ ≤ (1 + 4 * Real.pi^2) * (1 + ‖ξ‖)^2 := by
      unfold frequencyWeight
      have h₁ : 1 ≤ (1 + ‖ξ‖)^2 := by nlinarith [norm_nonneg ξ, sq_nonneg ‖ξ‖]
      have h₂ : ‖ξ‖^2 ≤ (1 + ‖ξ‖)^2 := by nlinarith [norm_nonneg ξ]
      nlinarith [mul_le_mul_of_nonneg_left h₂ (by positivity : 0 ≤ 4*Real.pi^2)]
    calc
      _ ≤ 2 * (((1 + 4 * Real.pi^2) * (1 + ‖ξ‖)^2) * ‖G ξ‖^2) := by gcongr
      _ = _ := by ring
  apply integral_mono hInt hUpper
  intro ξ
  have hCoeff : (1 + ‖ξ‖)^2 ≤ 2 * frequencyWeight ξ := by
    unfold frequencyWeight
    have hPi : 1 ≤ 4 * Real.pi^2 := by
      have h := (sq_le_sq₀ (by norm_num : 0 ≤ (2 : ℝ)) Real.pi_pos.le).mpr Real.two_le_pi
      linarith
    nlinarith [sq_nonneg (1 - ‖ξ‖), mul_nonneg (sub_nonneg.mpr hPi) (sq_nonneg ‖ξ‖)]
  calc
    _ ≤ (2 * frequencyWeight ξ) * ‖G ξ‖^2 := mul_le_mul_of_nonneg_right hCoeff (sq_nonneg _)
    _ = _ := by ring

end Burnett.Analysis.FirstOrderDyadic
