import Burnett.Analysis.H1FourierEnergy

/-!
# HminusWeightedDual

Paper-specific Hminus support; scope and remaining geometric obligations are recorded separately.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.Analysis.HminusWeightedDual
open MeasureTheory Filter
open scoped Topology ContDiff FourierTransform RealInnerProductSpace
open Burnett.X02.SobolevTestJet Burnett.X02.TestJetPairing
open Burnett.Fourier

theorem frequencyWeight_one_le (ξ : Space) : 1 ≤ frequencyWeight ξ := by
  unfold frequencyWeight
  exact le_add_of_nonneg_right (by positivity)

theorem test_frequency_energy_integrable (φ : D) :
    Integrable (fun ξ => frequencyWeight ξ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2) := by
  have hi (i : Fin 4) : Integrable (fun ξ =>
      (4 * Real.pi^2 * (ξ i)^2) * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2) := by
    apply (fourier_norm_sq_integrable
      (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single i 1) (complexTest φ))).congr
    exact Eventually.of_forall (fourier_coordinate_pderiv_norm_sq φ i)
  apply ((fourier_norm_sq_integrable (complexTest φ)).add
    (integrable_finset_sum Finset.univ (fun i _ => hi i))).congr
  filter_upwards with ξ
  have hξ : ‖ξ‖^2 = ∑ i : Fin 4, (ξ i)^2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  change ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2 +
    (∑ i : Fin 4, (4 * Real.pi^2 * (ξ i)^2) * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖^2) = _
  rw [frequencyWeight, hξ]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  ring

def negativeSource (f : SchwartzMap Space ℂ) (ξ : Space) : ℝ :=
  ‖𝓕 (f : Space → ℂ) ξ‖ / Real.sqrt (frequencyWeight ξ)

def positiveTest (φ : D) (ξ : Space) : ℝ :=
  Real.sqrt (frequencyWeight ξ) * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖

def negativeEnergy (f : SchwartzMap Space ℂ) : ℝ :=
  ∫ ξ, ‖𝓕 (f : Space → ℂ) ξ‖^2 / frequencyWeight ξ

theorem negativeSource_memLp (f : SchwartzMap Space ℂ) :
    MemLp (negativeSource f) 2 (volume : Measure Space) := by
  have hc : Continuous (negativeSource f) :=
    (SchwartzMap.fourierTransformCLM ℂ f).continuous.norm.div frequencyWeight_continuous.sqrt
      (fun ξ => ne_of_gt (Real.sqrt_pos.mpr (frequencyWeight_pos ξ)))
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply (fourier_norm_sq_integrable f).mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (sq_nonneg _), Real.norm_eq_abs, sq_abs]
  have heq : (negativeSource f ξ)^2 = ‖𝓕 (f : Space → ℂ) ξ‖^2 / frequencyWeight ξ := by
    unfold negativeSource
    rw [div_pow, Real.sq_sqrt (le_of_lt (frequencyWeight_pos ξ))]
  rw [heq]
  exact div_le_self (sq_nonneg _) (frequencyWeight_one_le ξ)

theorem positiveTest_memLp (φ : D) : MemLp (positiveTest φ) 2 (volume : Measure Space) := by
  have hc : Continuous (positiveTest φ) := frequencyWeight_continuous.sqrt.mul
    (SchwartzMap.fourierTransformCLM ℂ (complexTest φ)).continuous.norm
  apply (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).mpr
  apply (test_frequency_energy_integrable φ).congr
  filter_upwards with ξ
  simp only [positiveTest, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (le_of_lt (frequencyWeight_pos ξ))]

theorem negativeSource_toLp_norm_sq (f : SchwartzMap Space ℂ) :
    ‖(negativeSource_memLp f).toLp (negativeSource f)‖^2 = negativeEnergy f := by
  rw [real_toLp_norm_sq]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [negativeSource, Real.norm_eq_abs, sq_abs, div_pow,
    Real.sq_sqrt (le_of_lt (frequencyWeight_pos ξ))]

theorem negativeSource_toLp_norm (f : SchwartzMap Space ℂ) :
    ‖(negativeSource_memLp f).toLp (negativeSource f)‖ = Real.sqrt (negativeEnergy f) := by
  rw [← negativeSource_toLp_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem positiveTest_toLp_norm (φ : D) :
    ‖(positiveTest_memLp φ).toLp (positiveTest φ)‖ = ‖J φ‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [real_toLp_norm_sq, test_jet_fourier_energy]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [positiveTest, Real.norm_eq_abs, sq_abs, mul_pow,
    Real.sq_sqrt (le_of_lt (frequencyWeight_pos ξ))]

theorem negative_positive_product (f : SchwartzMap Space ℂ) (φ : D) (ξ : Space) :
    negativeSource f ξ * positiveTest φ ξ =
      ‖𝓕 (f : Space → ℂ) ξ‖ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖ := by
  unfold negativeSource positiveTest
  rw [← mul_assoc, div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.mpr (frequencyWeight_pos ξ)))]

theorem fourier_product_integrable (f : SchwartzMap Space ℂ) (φ : D) :
    Integrable (fun ξ => ‖𝓕 (f : Space → ℂ) ξ‖ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖) := by
  apply (L2.integrable_inner (𝕜 := ℝ)
    ((negativeSource_memLp f).toLp (negativeSource f))
    ((positiveTest_memLp φ).toLp (positiveTest φ))).congr
  filter_upwards [(negativeSource_memLp f).coeFn_toLp,
    (positiveTest_memLp φ).coeFn_toLp] with ξ hξ hφ
  rw [hξ, hφ, real_inner_eq_mul, negative_positive_product]

theorem fourier_weighted_cauchy (f : SchwartzMap Space ℂ) (φ : D) :
    (∫ ξ, ‖𝓕 (f : Space → ℂ) ξ‖ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖) ≤
      Real.sqrt (negativeEnergy f) * ‖J φ‖ := by
  have heq : inner ℝ ((negativeSource_memLp f).toLp (negativeSource f))
      ((positiveTest_memLp φ).toLp (positiveTest φ)) =
      ∫ ξ, ‖𝓕 (f : Space → ℂ) ξ‖ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(negativeSource_memLp f).coeFn_toLp,
      (positiveTest_memLp φ).coeFn_toLp] with ξ hξ hφ
    rw [hξ, hφ, real_inner_eq_mul, negative_positive_product]
  have hb := real_inner_le_norm ((negativeSource_memLp f).toLp (negativeSource f))
    ((positiveTest_memLp φ).toLp (positiveTest φ))
  rw [heq, negativeSource_toLp_norm, positiveTest_toLp_norm] at hb
  exact hb

theorem schwartz_inner_norm_le_weighted (f : SchwartzMap Space ℂ) (φ : D) :
    ‖inner ℂ (f.toLp 2 volume) ((complexTest φ).toLp 2 volume)‖ ≤
      Real.sqrt (negativeEnergy f) * ‖J φ‖ := by
  have h := (fourierL2Equiv (V := Space)).inner_map_map
    (f.toLp 2 volume) ((complexTest φ).toLp 2 volume)
  rw [fourierL2Equiv_schwartz, fourierL2Equiv_schwartz] at h
  rw [← h, L2.inner_def]
  calc
    _ ≤ ∫ ξ, ‖inner ℂ
        ((SchwartzMap.fourierTransformCLM ℂ f).toLp 2 volume ξ)
        ((SchwartzMap.fourierTransformCLM ℂ (complexTest φ)).toLp 2 volume ξ)‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ ξ, ‖𝓕 (f : Space → ℂ) ξ‖ * ‖𝓕 (complexTest φ : Space → ℂ) ξ‖ := by
      apply integral_congr_ae
      filter_upwards [(SchwartzMap.fourierTransformCLM ℂ f).coeFn_toLp 2 volume,
        (SchwartzMap.fourierTransformCLM ℂ (complexTest φ)).coeFn_toLp 2 volume] with ξ hf hφ
      rw [hf, hφ]
      simp only [RCLike.inner_apply, norm_mul, RCLike.norm_conj, mul_comm,
        SchwartzMap.fourierTransformCLM_apply]
    _ ≤ _ := fourier_weighted_cauchy f φ

def complexSource (f : Space → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    SchwartzMap Space ℂ :=
  (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hs)

def sourceFunctional (f : Space → ℝ) (hs : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ :=
  Burnett.X02.GraphDual.coefficientFunctional J
    (coefficients ((hs.continuous.memLp_of_hasCompactSupport hc).toLp f) (fun _ => 0))

theorem sourceFunctional_test (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (φ : D) :
    sourceFunctional f hs hc (Burnett.X02.GraphDual.testMap J φ) =
      ∫ x, f x * (φ : Space → ℝ) x := by
  have h := coefficientFunctional_test_of_memLp f (fun _ : Fin 4 => (0 : Space → ℝ))
    (hs.continuous.memLp_of_hasCompactSupport hc) (fun _ => MemLp.zero) φ
  simpa only [MemLp.toLp_zero, Pi.zero_apply, zero_mul, integral_zero,
    Finset.sum_const_zero, sub_zero, sourceFunctional] using h

theorem complexSource_inner_norm_eq (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (φ : D) :
    ‖inner ℂ ((complexSource f hs hc).toLp 2 volume) ((complexTest φ).toLp 2 volume)‖ =
      |∫ x, f x * (φ : Space → ℝ) x| := by
  have heq : inner ℂ ((complexSource f hs hc).toLp 2 volume) ((complexTest φ).toLp 2 volume) =
      ((∫ x, f x * (φ : Space → ℝ) x : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, ((f x * (φ : Space → ℝ) x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [(complexSource f hs hc).coeFn_toLp 2 volume,
          (complexTest φ).coeFn_toLp 2 volume] with x hf hφ
        rw [hf, hφ]
        change inner ℂ (f x : ℂ) ((φ : Space → ℝ) x : ℂ) = _
        simp [RCLike.inner_apply, mul_comm]
      _ = _ := integral_ofReal
  rw [heq, Complex.norm_real, Real.norm_eq_abs]

theorem sourceFunctional_test_bound (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) (φ : D) :
    |sourceFunctional f hs hc (Burnett.X02.GraphDual.testMap J φ)| ≤
      Real.sqrt (negativeEnergy (complexSource f hs hc)) * ‖J φ‖ := by
  rw [sourceFunctional_test]
  have h := schwartz_inner_norm_le_weighted (complexSource f hs hc) φ
  rw [complexSource_inner_norm_eq] at h
  exact h

theorem sourceFunctional_opnorm_le_weighted (f : Space → ℝ) (hs : ContDiff ℝ ∞ f)
    (hc : HasCompactSupport f) :
    ‖sourceFunctional f hs hc‖ ≤ Real.sqrt (negativeEnergy (complexSource f hs hc)) := by
  apply ContinuousLinearMap.opNorm_le_bound (sourceFunctional f hs hc) (Real.sqrt_nonneg _)
  intro x
  let S : Set (Burnett.X02.GraphDual.Graph J) := {x |
    ‖sourceFunctional f hs hc x‖ ≤ Real.sqrt (negativeEnergy (complexSource f hs hc)) * ‖x‖}
  have hclosed : IsClosed S := isClosed_le (sourceFunctional f hs hc).continuous.norm
    (continuous_const.mul continuous_norm)
  have hsub : Set.range (Burnett.X02.GraphDual.testMap J) ⊆ S := by
    rintro _ ⟨φ, rfl⟩
    change ‖sourceFunctional f hs hc (Burnett.X02.GraphDual.testMap J φ)‖ ≤
      Real.sqrt (negativeEnergy (complexSource f hs hc)) * ‖J φ‖
    simpa only [Real.norm_eq_abs] using sourceFunctional_test_bound f hs hc φ
  exact (hclosed.closure_subset_iff.mpr hsub) (Burnett.X02.GraphDual.denseRange_testMap J x)

theorem sourceFunctional_tendsto_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hc : ∀ n, HasCompactSupport (f n))
    (hE : Tendsto (fun n => negativeEnergy (complexSource (f n) (hs n) (hc n))) atTop (𝓝 0)) :
    Tendsto (fun n => sourceFunctional (f n) (hs n) (hc n)) atTop (𝓝 0) := by
  have hbound : Tendsto (fun n => Real.sqrt (negativeEnergy (complexSource (f n) (hs n) (hc n))))
      atTop (𝓝 0) := by simpa using hE.sqrt
  apply (Metric.tendsto_nhds (u := fun n => sourceFunctional (f n) (hs n) (hc n))
    (a := (0 : Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ))).mpr
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hbound) ε hε] with n hn
  rw [dist_zero_right (sourceFunctional (f n) (hs n) (hc n))]
  have hsmall : Real.sqrt (negativeEnergy (complexSource (f n) (hs n) (hc n))) < ε := by
    simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hn
  exact (sourceFunctional_opnorm_le_weighted (f n) (hs n) (hc n)).trans_lt hsmall

end Burnett.Analysis.HminusWeightedDual
