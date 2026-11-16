import Burnett.Analysis.IBP.CompactIBP
import Burnett.Analysis.Cubic.FrequencyBounds
import Burnett.Analysis.Sobolev.TestJet

noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology BigOperators

namespace Burnett.CubicDistribution

open CubicExplicit CubicFrequencies
open X02.CompactIBP (cosine_integral_bound)

theorem test_integral_bound {φ F : Space → ℝ} (hφ : Continuous φ)
    (hcφ : HasCompactSupport φ) (hF : Continuous F)
    {C : ℝ} (h : ∀ x, |F x| ≤ C) :
    |∫ x, φ x * F x| ≤ C * (∫ x, |φ x|) := by
  have hp : Integrable (fun x => φ x * F x) :=
    (hφ.mul hF).integrable_of_hasCompactSupport hcφ.mul_right
  have hiφ : Integrable (fun x : Space => |φ x|) :=
    (hφ.integrable_of_hasCompactSupport hcφ).abs
  calc
    _ ≤ ∫ x, ‖φ x * F x‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => φ x * F x)
    _ ≤ ∫ x, C * |φ x| := by
      apply integral_mono hp.norm (hiφ.const_mul C)
      intro x
      change ‖φ x * F x‖ ≤ C * |φ x|
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, mul_comm C]
      exact mul_le_mul_of_nonneg_left (h x) (abs_nonneg _)
    _ = _ := integral_const_mul _ _

theorem mode_integral_tendsto_zero (φ : X02.SobolevTestJet.D) (i : Mode) :
    Tendsto (fun n => ∫ x : Space, (φ : Space → ℝ) x * Real.cos (phase n i x))
      atTop (𝓝 0) := by
  let Z : ℝ := ∫ x : Space, |fderiv ℝ (φ : Space → ℝ) x (basis 0)|
  have hZ : 0 ≤ Z := integral_nonneg (fun _ => abs_nonneg _)
  have hb : ∀ᶠ n in atTop,
      ‖∫ x : Space, (φ : Space → ℝ) x * Real.cos (phase n i x)‖ ≤ Z / (2 * N n) := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have he := cosine_integral_bound φ.property.1 φ.property.2 (phase n i) (basis 0)
      (phase_time_ne_zero_of_two_le n hn i)
    rw [Real.norm_eq_abs]
    exact he.trans (div_le_div_of_nonneg_left hZ (mul_pos (by norm_num) (N_pos n))
      (phase_time_abs_lower_of_two_le n hn i))
  apply squeeze_zero_norm' hb
  have ht := tendsto_inv_N_zero.const_mul (Z / 2)
  have hf : (fun n => Z / (2*N n)) = fun n => (Z/2)*(N n)⁻¹ := by
    funext n
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  rw [hf]
  simpa only [mul_zero] using ht

theorem remainder_integral_tendsto_zero (φ : X02.SobolevTestJet.D) :
    Tendsto (fun n => ∫ x : Space, (φ : Space → ℝ) x * cubicRemainder ((N n)^2) (N n) x)
      atTop (𝓝 0) := by
  have hb (n : ℕ) :
      ‖∫ x : Space, (φ : Space → ℝ) x * cubicRemainder ((N n)^2) (N n) x‖ ≤
        (2 / N n) * (∫ x : Space, |(φ : Space → ℝ) x|) := by
    have hs : ContDiff ℝ ∞ (cubicRemainder ((N n)^2) (N n)) := by
      unfold cubicRemainder
      fun_prop
    simpa only [Real.norm_eq_abs] using
      test_integral_bound φ.property.1.continuous φ.property.2 hs.continuous
        (cubicRemainder_sequence_abs_le n)
  apply squeeze_zero_norm hb
  have ht := (tendsto_inv_N_zero.const_mul 2).mul_const
    (∫ x : Space, |(φ : Space → ℝ) x|)
  simpa only [div_eq_mul_inv, zero_mul, mul_zero] using ht

theorem mode_integrable (φ : X02.SobolevTestJet.D) (n : ℕ) (i : Mode) :
    Integrable (fun x : Space => (φ : Space → ℝ) x * Real.cos (phase n i x)) := by
  exact (φ.property.1.continuous.mul
    (Real.continuous_cos.comp (phase n i).continuous)).integrable_of_hasCompactSupport
    φ.property.2.mul_right

theorem oscillation_integrable (φ : X02.SobolevTestJet.D) (n : ℕ) :
    Integrable (fun x : Space => (φ : Space → ℝ) x * oscillation n x) := by
  have hcont : Continuous (oscillation n) := by
    unfold oscillation
    fun_prop
  exact (φ.property.1.continuous.mul hcont).integrable_of_hasCompactSupport φ.property.2.mul_right

theorem remainder_smooth (n : ℕ) :
    ContDiff ℝ ∞ (cubicRemainder ((N n)^2) (N n)) := by
  unfold cubicRemainder
  fun_prop

theorem remainder_integrable (φ : X02.SobolevTestJet.D) (n : ℕ) :
    Integrable (fun x : Space => (φ : Space → ℝ) x * cubicRemainder ((N n)^2) (N n) x) :=
  (φ.property.1.continuous.mul (remainder_smooth n).continuous).integrable_of_hasCompactSupport
    φ.property.2.mul_right

/-- Every summand is integrable before exchanging the finite sum and integral. -/
theorem oscillation_integral_eq_sum (φ : X02.SobolevTestJet.D) (n : ℕ) :
    (∫ x : Space, (φ : Space → ℝ) x * oscillation n x) =
      ∑ i : Mode, coefficient i * (∫ x : Space, (φ : Space → ℝ) x * Real.cos (phase n i x)) := by
  have hm (i : Mode) : Integrable (fun x : Space =>
      coefficient i * ((φ : Space → ℝ) x * Real.cos (phase n i x))) :=
    (mode_integrable φ n i).const_mul (coefficient i)
  have hf : (fun x : Space => (φ : Space → ℝ) x * oscillation n x) =
      fun x => ∑ i : Mode, coefficient i * ((φ : Space → ℝ) x * Real.cos (phase n i x)) := by
    funext x
    simp only [oscillation, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hf, integral_finset_sum Finset.univ (fun i _ => hm i)]
  apply Finset.sum_congr rfl
  intro i hi
  exact integral_const_mul _ _

theorem oscillation_integral_tendsto_zero (φ : X02.SobolevTestJet.D) :
    Tendsto (fun n => ∫ x : Space, (φ : Space → ℝ) x * oscillation n x) atTop (𝓝 0) := by
  have hm (i : Mode) : Tendsto
      (fun n => coefficient i * (∫ x : Space, (φ : Space → ℝ) x * Real.cos (phase n i x)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (mode_integral_tendsto_zero φ i).const_mul (coefficient i)
  have hsum := tendsto_finset_sum Finset.univ (fun i _ => hm i)
  have hf : (fun n => ∫ x : Space, (φ : Space → ℝ) x * oscillation n x) =
      fun n => ∑ i : Mode, coefficient i *
        (∫ x : Space, (φ : Space → ℝ) x * Real.cos (phase n i x)) :=
    funext (oscillation_integral_eq_sum φ)
  rw [hf]
  simpa only [Finset.sum_const_zero] using hsum

/-- The same explicit scalar pair supplies the exact integrand decomposition. -/
theorem cubic_test_integrand_eq (φ : X02.SobolevTestJet.D) (n : ℕ) :
    (fun x : Space => (φ : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x)) =
    fun x => (-(1/4) : ℝ) * (φ : Space → ℝ) x +
      (φ : Space → ℝ) x * oscillation n x +
      (φ : Space → ℝ) x * cubicRemainder ((N n)^2) (N n) x := by
  funext x
  rw [cubicSequence_eq_constant_oscillation_remainder]
  ring

theorem cubic_integrable (φ : X02.SobolevTestJet.D) (n : ℕ) :
    Integrable (fun x : Space => (φ : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x)) := by
  rw [cubic_test_integrand_eq]
  exact (((φ.property.1.continuous.integrable_of_hasCompactSupport φ.property.2).const_mul (-(1/4):ℝ)).add
    (oscillation_integrable φ n)).add (remainder_integrable φ n)

theorem cubic_integral_eq_parts (φ : X02.SobolevTestJet.D) (n : ℕ) :
    (∫ x : Space, (φ : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x)) =
      (-(1/4):ℝ) * (∫ x : Space, (φ : Space → ℝ) x) +
        (∫ x : Space, (φ : Space → ℝ) x * oscillation n x) +
        (∫ x : Space, (φ : Space → ℝ) x * cubicRemainder ((N n)^2) (N n) x) := by
  have hφ : Integrable (φ : Space → ℝ) :=
    φ.property.1.continuous.integrable_of_hasCompactSupport φ.property.2
  have hc := hφ.const_mul (-(1/4):ℝ)
  have ho := oscillation_integrable φ n
  have hr := remainder_integrable φ n
  have hsum := integral_add (hc.add ho) hr
  simp only [Pi.add_apply] at hsum
  have hpair := integral_add hc ho
  rw [cubic_test_integrand_eq, hsum, hpair, integral_const_mul]

/-- Distributional convergence is expressed on every actual C∞ compactly
supported test with its actual, integrable Bochner pairing. -/
theorem cubic_integral_tendsto (φ : X02.SobolevTestJet.D) :
    Tendsto (fun n => ∫ x : Space, (φ : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x))
      atTop (𝓝 ((-(1/4):ℝ) * (∫ x : Space, (φ : Space → ℝ) x))) := by
  have hc : Tendsto (fun _ : ℕ => (-(1/4):ℝ) * (∫ x : Space, (φ : Space → ℝ) x))
      atTop (𝓝 ((-(1/4):ℝ) * (∫ x : Space, (φ : Space → ℝ) x))) := tendsto_const_nhds
  have ht := (hc.add (oscillation_integral_tendsto_zero φ)).add
    (remainder_integral_tendsto_zero φ)
  have hf : (fun n => ∫ x : Space, (φ : Space → ℝ) x *
      (nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x)) =
      fun n => (-(1/4):ℝ) * (∫ x : Space, (φ : Space → ℝ) x) +
        (∫ x : Space, (φ : Space → ℝ) x * oscillation n x) +
        (∫ x : Space, (φ : Space → ℝ) x * cubicRemainder ((N n)^2) (N n) x) :=
    funext (cubic_integral_eq_parts φ)
  rw [hf]
  simpa only [add_zero] using ht

#print axioms mode_integral_tendsto_zero
#print axioms remainder_integral_tendsto_zero
#print axioms oscillation_integral_tendsto_zero
#print axioms cubic_integral_tendsto

end Burnett.CubicDistribution
