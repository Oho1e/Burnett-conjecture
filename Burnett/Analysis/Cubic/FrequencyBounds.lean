import Burnett.Analysis.Cubic.Explicit
import Mathlib.Topology.MetricSpace.Pseudo.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean

noncomputable section

namespace Burnett.CubicFrequencies

open scoped BigOperators Topology
open Filter
open CubicExplicit

abbrev Mode := Fin 7

/-- The seven actual continuous linear phases occurring in the exact expansion. -/
def phase (n : ℕ) (i : Mode) : Space →L[ℝ] ℝ :=
  if i = 0 then (2*N n) • v else
  if i = 1 then (4*N n) • v else
  if i = 2 then (2*(N n)^2) • u else
  if i = 3 then (2*N n) • v + (2*(N n)^2) • u else
  if i = 4 then (2*N n) • v - (2*(N n)^2) • u else
  if i = 5 then (4*N n) • v + (2*(N n)^2) • u else
    (4*N n) • v - (2*(N n)^2) • u

def coefficient (i : Mode) : ℝ :=
  if i.val = 0 then -(1/2) else if i.val = 5 then -(1/8) else if i.val = 6 then -(1/8) else -(1/4)

def oscillation (n : ℕ) (x : Space) : ℝ := ∑ i : Mode, coefficient i * Real.cos (phase n i x)

theorem sum_abs_coefficients : (∑ i : Mode, |coefficient i|) = 7/4 := by
  norm_num [coefficient, Fin.sum_univ_succ, Fin.reduceEq, Fin.reduceSucc, Fin.reduceFinMk]

/-- The frequency is evaluated from the actual linear map on the actual time
unit vector, not introduced as an independently specified scalar. -/
theorem phase_time_abs_lower (n : ℕ) (hN : 3 ≤ N n) (i : Mode) :
    2*N n ≤ |phase n i (basis 0)| := by
  have hpos := N_pos n
  have hsq : 3*N n ≤ (N n)^2 := by
    nlinarith [mul_nonneg hpos.le (sub_nonneg.mpr hN)]
  fin_cases i <;>
    simp [phase, ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, smul_eq_mul, abs_of_pos (N_pos n)]
  all_goals
    first
    | nlinarith [hsq]
    | rw [abs_of_nonneg (by nlinarith [hsq])]; nlinarith [hsq]
    | rw [abs_of_nonpos (by nlinarith [hsq])]; nlinarith [hsq]

theorem phase_time_ne_zero (n : ℕ) (hN : 3 ≤ N n) (i : Mode) :
    phase n i (basis 0) ≠ 0 := by
  intro h
  have hb := phase_time_abs_lower n hN i
  rw [h, abs_zero] at hb
  have hp := N_pos n
  linarith

theorem N_ge_three (n : ℕ) (hn : 2 ≤ n) : 3 ≤ N n := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  unfold N
  linarith

theorem phase_time_abs_lower_of_two_le (n : ℕ) (hn : 2 ≤ n) (i : Mode) :
    2*N n ≤ |phase n i (basis 0)| := phase_time_abs_lower n (N_ge_three n hn) i

theorem phase_time_ne_zero_of_two_le (n : ℕ) (hn : 2 ≤ n) (i : Mode) :
    phase n i (basis 0) ≠ 0 := phase_time_ne_zero n (N_ge_three n hn) i

theorem cubicMain_eq_oscillation (n : ℕ) (x : Space) :
    cubicMain ((N n)^2) (N n) x = -(1/4) + oscillation n x := by
  have h := seven_modes (N n*v x) ((N n)^2*u x)
  simp only [u_apply, v_apply] at h
  unfold cubicMain oscillation
  simp only [mul_assoc] at h ⊢
  simp [phase, coefficient, Fin.sum_univ_succ, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, smul_eq_mul, mul_assoc,
    Fin.reduceEq, Fin.reduceSucc]
  nlinarith only [h]

theorem cubicSequence_eq_constant_oscillation_remainder (n : ℕ) (x : Space) :
    nullForm (fSequence n) (wSequence n) x * D 0 (fSequence n) x =
      -(1/4) + oscillation n x + cubicRemainder ((N n)^2) (N n) x := by
  rw [cubicSequence_decomposition, cubicMain_eq_oscillation]

theorem tendsto_N_atTop : Tendsto N atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro b
  obtain ⟨m, hm⟩ := exists_nat_gt b
  refine ⟨m, ?_⟩
  intro n hn
  have hn' : (m : ℝ) ≤ n := by exact_mod_cast hn
  unfold N
  linarith

theorem tendsto_inv_N_zero : Tendsto (fun n => (N n)⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_N_atTop

theorem fSequence_abs_le_inv_N (n : ℕ) (x : Space) : |fSequence n x| ≤ (N n)⁻¹ := by
  have h := fSequence_abs_le n x
  rw [← inv_pow] at h
  have hi0 : 0 ≤ (N n)⁻¹ := inv_nonneg.mpr (N_pos n).le
  have hi1 : (N n)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (N_ge_one n)
  nlinarith [mul_nonneg hi0 (sub_nonneg.mpr hi1)]

theorem wSequence_abs_le_inv_N (n : ℕ) (x : Space) : |wSequence n x| ≤ (N n)⁻¹ := by
  have h := wSequence_abs_le n x
  have hi0 : 0 ≤ (N n)⁻¹ := inv_nonneg.mpr (N_pos n).le
  rw [mul_inv] at h
  norm_num at h
  linarith

/-- Global uniform convergence, stronger than the manuscript's local version. -/
theorem tendstoUniformly_fSequence : TendstoUniformly fSequence (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hn : ∀ᶠ n in atTop, (N n)⁻¹ < ε :=
    tendsto_inv_N_zero.eventually (Iio_mem_nhds hε)
  filter_upwards [hn] with n hn
  intro x
  simpa only [dist_zero_left, Real.norm_eq_abs] using (fSequence_abs_le_inv_N n x).trans_lt hn

theorem tendstoUniformly_wSequence : TendstoUniformly wSequence (fun _ => 0) atTop := by
  apply Metric.tendstoUniformly_iff.mpr
  intro ε hε
  have hn : ∀ᶠ n in atTop, (N n)⁻¹ < ε :=
    tendsto_inv_N_zero.eventually (Iio_mem_nhds hε)
  filter_upwards [hn] with n hn
  intro x
  simpa only [dist_zero_left, Real.norm_eq_abs] using (wSequence_abs_le_inv_N n x).trans_lt hn

end Burnett.CubicFrequencies
