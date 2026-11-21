import Burnett.Analysis.HminusWeightedDual
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.HminusReverse

open MeasureTheory Set Filter Burnett.Fourier Burnett.Analysis.HminusWeightedDual
open Burnett.X02.SobolevTestJet
open scoped ContDiff FourierTransform Topology BigOperators

def fourierH1Energy (u : SchwartzMap Space ℂ) : ℝ :=
  ∫ ξ, frequencyWeight ξ * ‖𝓕 (u : Space → ℂ) ξ‖ ^ 2

def schwartzH1Energy (u : SchwartzMap Space ℂ) : ℝ :=
  ‖u.toLp 2 volume‖ ^ 2 +
    ∑ j : Fin 4, ‖(SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u).toLp 2 volume‖ ^ 2

private theorem fourier_pderiv_norm_sq (u : SchwartzMap Space ℂ) (j : Fin 4) (ξ : Space) :
    ‖𝓕 (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u : Space → ℂ) ξ‖ ^ 2 =
      (4 * Real.pi ^ 2 * (ξ j) ^ 2) * ‖𝓕 (u : Space → ℂ) ξ‖ ^ 2 := by
  rw [fourier_pderiv]
  simp only [norm_mul, mul_pow, EuclideanSpace.inner_single_right, mul_one,
    Complex.norm_I, one_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  norm_num

private theorem toLp_norm_sq_eq_fourier (u : SchwartzMap Space ℂ) :
    ‖u.toLp 2 volume‖ ^ 2 = ∫ x, ‖𝓕 (u : Space → ℂ) x‖ ^ 2 := by
  rw [schwartz_parseval, l2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [u.coeFn_toLp 2 volume] with x hx
  rw [hx]

/-- Plancherel in the same weight as the project H¹ graph, for each actual
complex Schwartz test and all four of its directional derivatives. -/
theorem schwartzH1Energy_eq_fourierH1Energy (u : SchwartzMap Space ℂ) :
    schwartzH1Energy u = fourierH1Energy u := by
  have hL (j : Fin 4) : Integrable (fun ξ : Space =>
      (4 * Real.pi ^ 2 * (ξ j) ^ 2) * ‖𝓕 (u : Space → ℂ) ξ‖ ^ 2) := by
    exact (fourier_norm_sq_integrable (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u)).congr
      (Eventually.of_forall (fourier_pderiv_norm_sq u j))
  unfold schwartzH1Energy fourierH1Energy
  rw [toLp_norm_sq_eq_fourier u]
  have hEq (j : Fin 4) :
      ‖(SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) u).toLp 2 volume‖ ^ 2 =
        ∫ ξ : Space, (4 * Real.pi ^ 2 * (ξ j) ^ 2) * ‖𝓕 (u : Space → ℂ) ξ‖ ^ 2 := by
    rw [toLp_norm_sq_eq_fourier]
    exact integral_congr_ae (Eventually.of_forall (fourier_pderiv_norm_sq u j))
  simp_rw [hEq]
  rw [← integral_finset_sum _ (fun j _ => hL j),
    ← integral_add (fourier_norm_sq_integrable u) (integrable_finset_sum _ (fun j _ => hL j))]
  apply integral_congr_ae
  filter_upwards with ξ
  have hn : ‖ξ‖ ^ 2 = ∑ j : Fin 4, (ξ j) ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp only [Real.norm_eq_abs, sq_abs]
  rw [frequencyWeight, hn, ← Finset.sum_mul, ← Finset.mul_sum]
  ring

private theorem frequencyWeight_smooth : ContDiff ℝ ∞ frequencyWeight := by
  unfold frequencyWeight
  exact contDiff_const.add (contDiff_const.mul (contDiff_norm_sq ℝ))

def negativeDensity (f : SchwartzMap Space ℂ) (ξ : Space) : ℝ :=
  ‖𝓕 (f : Space → ℂ) ξ‖ ^ 2 / frequencyWeight ξ

theorem negativeDensity_nonneg (f : SchwartzMap Space ℂ) (ξ : Space) : 0 ≤ negativeDensity f ξ :=
  div_nonneg (sq_nonneg _) (frequencyWeight_pos ξ).le

theorem negativeDensity_integrable (f : SchwartzMap Space ℂ) : Integrable (negativeDensity f) := by
  have hc : Continuous (negativeDensity f) :=
    ((SchwartzMap.fourierTransformCLM ℂ f).continuous.norm.pow 2).div frequencyWeight_continuous
      (fun x => (frequencyWeight_pos x).ne')
  apply (fourier_norm_sq_integrable f).mono' hc.aestronglyMeasurable
  filter_upwards with x
  rw [Real.norm_of_nonneg (negativeDensity_nonneg f x)]
  exact div_le_self (sq_nonneg _) (frequencyWeight_one_le x)

private def frequencyWitness (f : SchwartzMap Space ℂ) (χ : D) : SchwartzMap Space ℂ :=
  (((test_compactSupport χ).comp_left Complex.ofReal_zero).mul_right :
    HasCompactSupport (fun ξ => ((χ : Space → ℝ) ξ : ℂ) *
      ((frequencyWeight ξ : ℂ)⁻¹ * (SchwartzMap.fourierTransformCLM ℂ f) ξ))).toSchwartzMap
      ((Complex.ofRealCLM.contDiff.comp (test_smooth χ)).mul
        (((Complex.ofRealCLM.contDiff.comp frequencyWeight_smooth).inv
          (fun x => Complex.ofReal_ne_zero.mpr (frequencyWeight_pos x).ne')).mul
          ((SchwartzMap.fourierTransformCLM ℂ f).smooth ⊤)))

def inverseFrequencyTest (f : SchwartzMap Space ℂ) (χ : D) : SchwartzMap Space ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (frequencyWitness f χ)

theorem inverseFrequencyTest_fourier (f : SchwartzMap Space ℂ) (χ : D) (x : Space) :
    𝓕 (inverseFrequencyTest f χ : Space → ℂ) x =
      ((χ : Space → ℝ) x : ℂ) * ((frequencyWeight x : ℂ)⁻¹ * 𝓕 (f : Space → ℂ) x) := by
  change (SchwartzMap.fourierTransformCLE ℂ (inverseFrequencyTest f χ)) x = _
  rw [inverseFrequencyTest, ContinuousLinearEquiv.apply_symm_apply]
  rfl

/-- The actual inverse test pairs with the Schwartz source by the truncated
negative-frequency energy, with the real coefficient and its sign preserved. -/
theorem inner_inverseFrequencyTest (f : SchwartzMap Space ℂ) (χ : D) :
    inner ℂ (f.toLp 2 volume) ((inverseFrequencyTest f χ).toLp 2 volume) =
      ((∫ ξ, (χ : Space → ℝ) ξ * negativeDensity f ξ : ℝ) : ℂ) := by
  have he := (fourierL2Equiv (V := Space)).inner_map_map
    (f.toLp 2 volume) ((inverseFrequencyTest f χ).toLp 2 volume)
  rw [← he, L2.inner_def, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [fourierL2Equiv_schwartz_ae f,
    fourierL2Equiv_schwartz_ae (inverseFrequencyTest f χ)] with x hf htest
  rw [hf, htest, inverseFrequencyTest_fourier]
  let y := 𝓕 (f : Space → ℂ) x
  have hn : (star y) * y = (‖y‖ ^ 2 : ℝ) := by
    rw [mul_comm, Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  change inner ℂ y (((χ : Space → ℝ) x : ℂ) * ((frequencyWeight x : ℂ)⁻¹ * y)) = _
  rw [RCLike.inner_apply]
  change ((χ : Space → ℝ) x : ℂ) * ((frequencyWeight x : ℂ)⁻¹ * y) * star y = _
  simp only [negativeDensity, ← show y = 𝓕 (f : Space → ℂ) x from rfl,
    Complex.ofReal_mul, div_eq_mul_inv, Complex.ofReal_inv]
  calc
    _ = ((χ : Space → ℝ) x : ℂ) * ((frequencyWeight x : ℂ)⁻¹ * (star y * y)) := by ring
    _ = _ := by rw [hn]; ring

private theorem negativeDensity_continuous (f : SchwartzMap Space ℂ) : Continuous (negativeDensity f) :=
  ((SchwartzMap.fourierTransformCLM ℂ f).continuous.norm.pow 2).div frequencyWeight_continuous
    (fun x => (frequencyWeight_pos x).ne')

/-- The full Sobolev energy of the inverse cutoff test is bounded by its
pairing with the actual source when the real frequency cutoff lies in [0,1]. -/
theorem inverseFrequencyTest_energy_le (f : SchwartzMap Space ℂ) (χ : D)
    (hχ₀ : ∀ x, 0 ≤ (χ : Space → ℝ) x) (hχ₁ : ∀ x, (χ : Space → ℝ) x ≤ 1) :
    schwartzH1Energy (inverseFrequencyTest f χ) ≤
      ∫ x, (χ : Space → ℝ) x * negativeDensity f x := by
  have he (x : Space) :
      frequencyWeight x * ‖𝓕 (inverseFrequencyTest f χ : Space → ℂ) x‖ ^ 2 =
        ((χ : Space → ℝ) x) ^ 2 * negativeDensity f x := by
    rw [inverseFrequencyTest_fourier]
    simp only [negativeDensity, norm_mul, Complex.norm_real, norm_inv, Real.norm_eq_abs,
      abs_of_nonneg (hχ₀ x), abs_of_pos (frequencyWeight_pos x), mul_pow, inv_pow, div_eq_mul_inv]
    field_simp [(frequencyWeight_pos x).ne']
  rw [schwartzH1Energy_eq_fourierH1Energy, fourierH1Energy]
  simp_rw [he]
  have hd := negativeDensity_continuous f
  have hp : HasCompactSupport (fun x => ((χ : Space → ℝ) x) ^ 2) := by
    simpa only [pow_two] using ((test_compactSupport χ).mul_right :
      HasCompactSupport (fun x => (χ : Space → ℝ) x * (χ : Space → ℝ) x))
  apply integral_mono
  · exact (((test_smooth χ).continuous.pow 2).mul hd).integrable_of_hasCompactSupport
      hp.mul_right
  · exact ((test_smooth χ).continuous.mul hd).integrable_of_hasCompactSupport
      ((test_compactSupport χ).mul_right)
  · intro x
    apply mul_le_mul_of_nonneg_right _ (negativeDensity_nonneg f x)
    simpa only [pow_two, mul_one] using mul_le_mul_of_nonneg_left (hχ₁ x) (hχ₀ x)

/-- The actual Fourier cutoff probes give the reverse squared norm bound
once the real dual estimate is available on the Schwartz test space. -/
theorem truncatedNegativeEnergy_le_sq (f : SchwartzMap Space ℂ) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ u : SchwartzMap Space ℂ,
      (inner ℂ (f.toLp 2 volume) (u.toLp 2 volume)).re ≤ C * Real.sqrt (schwartzH1Energy u))
    (χ : D) (hχ₀ : ∀ x, 0 ≤ (χ : Space → ℝ) x) (hχ₁ : ∀ x, (χ : Space → ℝ) x ≤ 1) :
    (∫ x, (χ : Space → ℝ) x * negativeDensity f x) ≤ C ^ 2 := by
  let Y := ∫ x, (χ : Space → ℝ) x * negativeDensity f x
  change Y ≤ C ^ 2
  have hY : 0 ≤ Y := integral_nonneg (fun x => mul_nonneg (hχ₀ x) (negativeDensity_nonneg f x))
  have hpair := hBound (inverseFrequencyTest f χ)
  rw [inner_inverseFrequencyTest, Complex.ofReal_re] at hpair
  have hle : Y ≤ C * Real.sqrt Y := hpair.trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (inverseFrequencyTest_energy_le f χ hχ₀ hχ₁)) hC)
  rcases eq_or_lt_of_le (Real.sqrt_nonneg Y) with hzero | hpos
  · have hh : Y = 0 := by rw [← Real.sq_sqrt hY, ← hzero, zero_pow (by decide)]
    exact hh.le.trans (sq_nonneg C)
  · have hm : Real.sqrt Y * Real.sqrt Y ≤ C * Real.sqrt Y := by
      rw [← pow_two, Real.sq_sqrt hY]
      exact hle
    rw [← Real.sq_sqrt hY]
    exact (sq_le_sq₀ (Real.sqrt_nonneg _) hC).mpr (le_of_mul_le_mul_right hm hpos)

private def growingFrequencyBump (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨(n : ℝ) + 1, (n : ℝ) + 2, by positivity, by linarith⟩

private def growingFrequencyTest (n : ℕ) : D :=
  ⟨growingFrequencyBump n, ⟨(growingFrequencyBump n).contDiff,
    (growingFrequencyBump n).hasCompactSupport⟩⟩

private theorem growingFrequencyTest_eventually_one (x : Space) :
    ∀ᶠ n in atTop, (growingFrequencyTest n : Space → ℝ) x = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  apply (growingFrequencyBump n).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
  change ‖x‖ ≤ (n : ℝ) + 1
  linarith

/-- Exhausting the whole frequency space proves the reverse bound for the
actual Schwartz Fourier energy. The truncated tests are all genuine Schwartz
functions and the limit uses one integrable majorant. -/
theorem negativeEnergy_le_sq_of_schwartz_tests (f : SchwartzMap Space ℂ) (C : ℝ)
    (hC : 0 ≤ C) (hBound : ∀ u : SchwartzMap Space ℂ,
      (inner ℂ (f.toLp 2 volume) (u.toLp 2 volume)).re ≤ C * Real.sqrt (schwartzH1Energy u)) :
    negativeEnergy f ≤ C ^ 2 := by
  have hχ₀ (n : ℕ) (x : Space) : 0 ≤ (growingFrequencyTest n : Space → ℝ) x :=
    (growingFrequencyBump n).nonneg
  have hχ₁ (n : ℕ) (x : Space) : (growingFrequencyTest n : Space → ℝ) x ≤ 1 :=
    (growingFrequencyBump n).le_one
  have hLim : Tendsto (fun n : ℕ => ∫ x, (growingFrequencyTest n : Space → ℝ) x *
      negativeDensity f x) atTop (𝓝 (negativeEnergy f)) := by
    apply tendsto_integral_filter_of_dominated_convergence (f := negativeDensity f) (negativeDensity f)
    · exact Eventually.of_forall (fun n => (((test_smooth (growingFrequencyTest n)).continuous).mul
        (negativeDensity_continuous f)).aestronglyMeasurable)
    · refine Eventually.of_forall (fun n => Eventually.of_forall (fun x => ?_))
      rw [Real.norm_of_nonneg (mul_nonneg (hχ₀ n x) (negativeDensity_nonneg f x))]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hχ₁ n x) (negativeDensity_nonneg f x)
    · exact negativeDensity_integrable f
    · refine Eventually.of_forall (fun x => ?_)
      apply tendsto_const_nhds.congr'
      filter_upwards [growingFrequencyTest_eventually_one x] with n hn
      rw [hn, one_mul]
  exact le_of_tendsto hLim (Eventually.of_forall (fun n =>
    truncatedNegativeEnergy_le_sq f C hC hBound (growingFrequencyTest n) (hχ₀ n) (hχ₁ n)))

end Burnett.Microlocal.HminusReverse
