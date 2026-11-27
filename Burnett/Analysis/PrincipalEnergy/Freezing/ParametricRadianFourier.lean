import Burnett.Analysis.PrincipalEnergy.Freezing.RadianShiftDifference
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal FourierTransform RealInnerProductSpace

/-- A polynomial bound sufficient for the joint Fourier integral and its
first derivative on the actual Schwartz inputs. -/
def RadianAverageGrowth (m : E × E → ℝ) : Prop :=
  ∃ A : ℝ, 0 ≤ A ∧ ∀ η ξ : E, ‖m (η, tau • ξ)‖ ≤ A * (1 + ‖η‖) * (1 + ‖ξ‖)

private def averageFrequencyPairing : (E × E) →L[ℝ] E →L[ℝ] ℝ :=
  -((innerSL ℝ).comp (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E))

private def averageMeasure : Measure (E × E) := (volume : Measure E).prod volume

private def averageSpectrum (m : E × E → ℝ) (f u : SchwartzMap E ℂ) (z : E × E) : ℂ :=
  (m (z.1, tau • z.2) : ℂ) * (𝓕 (f : E → ℂ) z.1 * 𝓕 (u : E → ℂ) z.2)

/-- The joint Fourier integral carries the actual output frequency \(\eta+\xi\). -/
def radianFourierAverage (m : E × E → ℝ) (f u : SchwartzMap E ℂ) : E → ℂ :=
  VectorFourier.fourierIntegral Real.fourierChar averageMeasure averageFrequencyPairing.toLinearMap₁₂
    (averageSpectrum m f u)

private theorem average_phase_eq (z : E × E) (x : E) :
    Complex.exp ((↑(-2 * Real.pi * averageFrequencyPairing.toLinearMap₁₂ z x) : ℂ) * Complex.I) =
      patchFourierPhase (z.1 + z.2) x := by
  change Complex.exp ((↑(-2 * Real.pi * -inner ℝ (z.1 + z.2) x) : ℂ) * Complex.I) = _
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, mul_neg, neg_mul, neg_neg]

private theorem fourier_weighted_one_integrable (f : SchwartzMap E ℂ) :
    Integrable (fun η : E => (1 + ‖η‖) * ‖𝓕 (f : E → ℂ) η‖) := by
  let U := SchwartzMap.fourierTransformCLM ℂ f
  have h := U.integrable.norm.add (U.integrable_pow_mul volume 1)
  apply h.congr
  filter_upwards with η
  change ‖U η‖ + ‖η‖ ^ 1 * ‖U η‖ = (1 + ‖η‖) * ‖U η‖
  rw [pow_one, add_mul, one_mul]

private theorem fourier_weighted_two_integrable (f : SchwartzMap E ℂ) :
    Integrable (fun η : E => (1 + ‖η‖) ^ 2 * ‖𝓕 (f : E → ℂ) η‖) := by
  let U := SchwartzMap.fourierTransformCLM ℂ f
  have h := (U.integrable.norm.add ((U.integrable_pow_mul volume 1).const_mul 2)).add
    (U.integrable_pow_mul volume 2)
  apply h.congr
  filter_upwards with η
  change ‖U η‖ + 2 * (‖η‖ ^ 1 * ‖U η‖) + ‖η‖ ^ 2 * ‖U η‖ = (1 + ‖η‖) ^ 2 * ‖U η‖
  rw [pow_one]
  ring

private theorem average_spectrum_integrable (m : E × E → ℝ) (meas : Measurable m)
    (grow : RadianAverageGrowth m) (f u : SchwartzMap E ℂ) :
    Integrable (averageSpectrum m f u) averageMeasure ∧
      Integrable (fun z => ‖z‖ * ‖averageSpectrum m f u z‖) averageMeasure := by
  obtain ⟨A, A0, growth⟩ := grow
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have fstM : Measurable (Prod.fst : E × E → E) := measurable_fst
  have sndM : Measurable (Prod.snd : E × E → E) := measurable_snd
  have scale : Measurable (fun z : E => tau • z) := (continuous_const.smul continuous_id).measurable
  have args : Measurable (fun z : E × E => (z.1, tau • z.2)) := fstM.prodMk (scale.comp sndM)
  have hS : Measurable (averageSpectrum m f u) :=
    (Complex.continuous_ofReal.measurable.comp (meas.comp args)).mul
      ((F.continuous.measurable.comp fstM).mul (U.continuous.measurable.comp sndM))
  have bound (z : E × E) : ‖averageSpectrum m f u z‖ ≤
      (A * ((1 + ‖z.1‖) * ‖F z.1‖)) * ((1 + ‖z.2‖) * ‖U z.2‖) := by
    simp only [averageSpectrum, norm_mul, Complex.norm_real]
    exact (mul_le_mul_of_nonneg_right (growth z.1 z.2)
      (mul_nonneg (norm_nonneg (F z.1)) (norm_nonneg (U z.2)))).trans_eq
      (by ring)
  constructor
  · exact (((fourier_weighted_one_integrable f).const_mul A).mul_prod
      (fourier_weighted_one_integrable u)).mono' hS.aestronglyMeasurable (Eventually.of_forall bound)
  · apply (((fourier_weighted_two_integrable f).const_mul A).mul_prod
      (fourier_weighted_two_integrable u)).mono' (continuous_norm.measurable.mul hS.norm).aestronglyMeasurable
    filter_upwards with z
    have pair_norm : ‖z‖ ≤ (1 + ‖z.1‖) * (1 + ‖z.2‖) := by
      rw [Prod.norm_def]
      apply max_le
      · nlinarith only [norm_nonneg z.1, norm_nonneg z.2, mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]
      · nlinarith only [norm_nonneg z.1, norm_nonneg z.2, mul_nonneg (norm_nonneg z.1) (norm_nonneg z.2)]
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact (mul_le_mul pair_norm (bound z) (norm_nonneg _)
      (mul_nonneg (by positivity) (by positivity))).trans_eq (by
        change _ = (A * ((1 + ‖z.1‖) ^ 2 * ‖F z.1‖)) * ((1 + ‖z.2‖) ^ 2 * ‖U z.2‖)
        ring)

private theorem average_product_integral (m : E × E → ℝ) (f u : SchwartzMap E ℂ) (x : E) :
    radianFourierAverage m f u x =
      ∫ z : E × E, patchFourierPhase (z.1 + z.2) x * averageSpectrum m f u z ∂averageMeasure := by
  rw [radianFourierAverage, Real.vector_fourierIntegral_eq_integral_exp_smul]
  simp only [smul_eq_mul, average_phase_eq]

private theorem average_product_integrable (m : E × E → ℝ) (meas : Measurable m)
    (grow : RadianAverageGrowth m) (f u : SchwartzMap E ℂ) (x : E) :
    Integrable (fun z : E × E => patchFourierPhase (z.1 + z.2) x * averageSpectrum m f u z)
      averageMeasure := by
  let args : E × E → E × E := fun z => (z.1 + z.2, x)
  have hargs : Continuous args := (continuous_fst.add continuous_snd).prodMk continuous_const
  have hphase := patch_fourier_phase_continuous.comp hargs
  exact (average_spectrum_integrable m meas grow f u).1.bdd_mul hphase.aestronglyMeasurable
    ⟨1, fun z => (patch_fourier_phase_norm (z.1 + z.2) x).le⟩

/-- Fubini identifies the joint integral with the weighted average of literal
one-frequency radian actions. -/
theorem radian_fourier_average_eq_integral (m : E × E → ℝ) (meas : Measurable m)
    (grow : RadianAverageGrowth m) (f u : SchwartzMap E ℂ) (x : E) :
    radianFourierAverage m f u x = ∫ η, (patchFourierPhase η x * 𝓕 (f : E → ℂ) η) *
      radianAction (fun ξ => m (η, ξ)) u x := by
  rw [average_product_integral, averageMeasure, integral_prod _ (average_product_integrable m meas grow f u x)]
  apply integral_congr_ae
  filter_upwards with η
  rw [radian_action_fourier_integral, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [averageSpectrum, patch_fourier_phase_add]
  ring

/-- Subtraction takes place on the actual product Fourier integrals. -/
theorem radian_fourier_average_sub (a b : E × E → ℝ) (ha : Measurable a) (hb : Measurable b)
    (ga : RadianAverageGrowth a) (gb : RadianAverageGrowth b) (f u : SchwartzMap E ℂ) :
    radianFourierAverage (fun z => a z - b z) f u =
      radianFourierAverage a f u - radianFourierAverage b f u := by
  funext x
  simp only [Pi.sub_apply, average_product_integral]
  rw [← integral_sub (average_product_integrable a ha ga f u x) (average_product_integrable b hb gb f u x)]
  apply integral_congr_ae
  filter_upwards with z
  simp only [averageSpectrum, Complex.ofReal_sub]
  ring

/-- One real coordinate derivative distributes over the two actual Fourier
inputs, with no derivative of the parameter-dependent multiplier. -/
theorem radian_fourier_average_coordinate (m : E × E → ℝ) (meas : Measurable m)
    (grow : RadianAverageGrowth m) (f u : SchwartzMap E ℂ) (j : Index) (x : E) :
    DifferentiableAt ℝ (radianFourierAverage m f u) x ∧
      fderiv ℝ (radianFourierAverage m f u) x (EuclideanSpace.single j 1) =
        radianFourierAverage m (energyPartial j f) u x + radianFourierAverage m f (energyPartial j u) x := by
  let S := averageSpectrum m f u
  let L := averageFrequencyPairing
  let e : E := EuclideanSpace.single j 1
  obtain ⟨hS, hS₁⟩ := average_spectrum_integrable m meas grow f u
  have h := VectorFourier.hasFDerivAt_fourierIntegral L hS hS₁ x
  refine ⟨h.differentiableAt, ?_⟩
  change fderiv ℝ (VectorFourier.fourierIntegral Real.fourierChar averageMeasure L.toLinearMap₁₂ S) x e = _
  rw [h.fderiv, Real.vector_fourierIntegral_eq_integral_exp_smul]
  have hSMul : Integrable (VectorFourier.fourierSMulRight L S) averageMeasure := by
    apply (hS₁.const_mul (2 * Real.pi * ‖L‖)).mono' hS.1.fourierSMulRight
    filter_upwards with z
    exact (VectorFourier.norm_fourierSMulRight_le L S z).trans_eq (by ring)
  have hPhase : Measurable (fun z : E × E => patchFourierPhase (z.1 + z.2) x) := by
    let args : E × E → E × E := fun z => (z.1 + z.2, x)
    have hargs : Continuous args := (continuous_fst.add continuous_snd).prodMk continuous_const
    exact (patch_fourier_phase_continuous.comp hargs).measurable
  have hD : Integrable (fun z : E × E =>
      patchFourierPhase (z.1 + z.2) x • VectorFourier.fourierSMulRight L S z) averageMeasure := by
    apply hSMul.norm.mono' (hPhase.aestronglyMeasurable.smul hSMul.aestronglyMeasurable)
    filter_upwards with z
    rw [norm_smul, patch_fourier_phase_norm, one_mul]
  simp only [L, average_phase_eq]
  rw [ContinuousLinearMap.integral_apply hD, average_product_integral, average_product_integral,
    ← integral_add (average_product_integrable m meas grow (energyPartial j f) u x)
      (average_product_integrable m meas grow f (energyPartial j u) x)]
  apply integral_congr_ae
  filter_upwards with z
  have coordinate : averageFrequencyPairing z e = -(z.1 j + z.2 j) := by
    change -inner ℝ (z.1 + z.2) (EuclideanSpace.single j 1) = _
    rw [EuclideanSpace.inner_single_right]
    simp
  simp only [ContinuousLinearMap.smul_apply, VectorFourier.fourierSMulRight_apply, L,
    coordinate, S, averageSpectrum, energyPartial_fourier, smul_eq_mul, Complex.real_smul,
    Complex.ofReal_neg, Complex.ofReal_add, tau]
  push_cast
  ring

end Burnett.A03
