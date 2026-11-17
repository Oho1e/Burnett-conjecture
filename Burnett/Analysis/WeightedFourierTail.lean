import Burnett.Analysis.LocalHminusFourier

/-!
# WeightedFourierTail

Paper-specific Hminus support; scope and remaining geometric obligations are recorded separately.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.HminusWeightedTail
open MeasureTheory Filter Set
open scoped Topology FourierTransform ContDiff
open Burnett.X02.SobolevTestJet

theorem frequencyWeight_one_le (ξ : Space) :
    1 ≤ 1 + 4 * Real.pi^2 * ‖ξ‖^2 :=
  le_add_of_nonneg_right (by positivity)

theorem frequencyWeight_ge_norm (ξ : Space) :
    ‖ξ‖ ≤ 1 + 4 * Real.pi^2 * ‖ξ‖^2 := by
  have hp : 1 ≤ 4 * Real.pi^2 := by
    nlinarith [Real.two_le_pi, sq_nonneg (Real.pi - 2)]
  have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg ‖ξ‖)
  nlinarith [sq_nonneg (‖ξ‖ - 1)]

theorem weighted_integrable {F : Space → ℝ} (hf : Integrable F)
    (hn : ∀ ξ, 0 ≤ F ξ) :
    Integrable (fun ξ => F ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2)) := by
  have hc : Continuous (fun ξ : Space => 1 + 4 * Real.pi^2 * ‖ξ‖^2) := by fun_prop
  have hi : Continuous (fun ξ : Space => (1 + 4 * Real.pi^2 * ‖ξ‖^2)⁻¹) :=
    hc.inv₀ (fun ξ => ne_of_gt (lt_of_lt_of_le zero_lt_one (frequencyWeight_one_le ξ)))
  have hm : AEStronglyMeasurable (fun ξ => F ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2)) volume := by
    simpa only [div_eq_mul_inv] using hf.aestronglyMeasurable.mul hi.aestronglyMeasurable
  apply hf.mono' hm
  apply Eventually.of_forall
  intro ξ
  rw [Real.norm_of_nonneg (div_nonneg (hn ξ) (by positivity))]
  exact div_le_self (hn ξ) (frequencyWeight_one_le ξ)

theorem weighted_split_bound {F : Space → ℝ} (hf : Integrable F)
    (hn : ∀ ξ, 0 ≤ F ξ) {C : ℝ} (hb : (∫ ξ, F ξ) ≤ C)
    {R : ℝ} (hR : 0 < R) :
    (∫ ξ, F ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2)) ≤
      (∫ ξ in Metric.closedBall (0 : Space) R, F ξ) + C / R := by
  let S := Metric.closedBall (0 : Space) R
  have hs : MeasurableSet S := measurableSet_closedBall
  have hw := weighted_integrable hf hn
  have hin : (∫ ξ in S, F ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2)) ≤ ∫ ξ in S, F ξ := by
    apply setIntegral_mono_on hw.integrableOn hf.integrableOn hs
    intro ξ _
    exact div_le_self (hn ξ) (frequencyWeight_one_le ξ)
  have hout : (∫ ξ in Sᶜ, F ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2)) ≤
      (∫ ξ in Sᶜ, F ξ) / R := by
    rw [← integral_div R F]
    apply setIntegral_mono_on hw.integrableOn (hf.div_const R).integrableOn hs.compl
    intro ξ hx
    have hnorm : R < ‖ξ‖ := by
      simpa only [S, Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
    exact div_le_div_of_nonneg_left (hn ξ) hR
      ((le_of_lt hnorm).trans (frequencyWeight_ge_norm ξ))
  have htail : (∫ ξ in Sᶜ, F ξ) ≤ C := by
    have hsplit := integral_add_compl hs hf
    have hpos : 0 ≤ ∫ ξ in S, F ξ := integral_nonneg (fun ξ => hn ξ)
    linarith
  have htotal := integral_add_compl hs hw
  have htail' := div_le_div_of_nonneg_right htail (le_of_lt hR)
  change _ ≤ (∫ ξ in S, F ξ) + C / R
  linarith

theorem weighted_energy_tendsto_zero {F : ℕ → Space → ℝ}
    (hf : ∀ n, Integrable (F n)) (hn : ∀ n ξ, 0 ≤ F n ξ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ n, (∫ ξ, F n ξ) ≤ C)
    (hl : ∀ R : ℝ, Tendsto (fun n => ∫ ξ in Metric.closedBall (0 : Space) R, F n ξ)
      atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ξ, F n ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2)) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let R : ℝ := 1 + 2 * C / ε
  have hR : 0 < R := by dsimp [R]; positivity
  have hRε : ε * R = ε + 2 * C := by
    dsimp [R]
    field_simp [ne_of_gt hε]
  have htail : C / R < ε / 2 := (div_lt_iff₀ hR).2 (by nlinarith)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp (hl R) (ε / 2) (by positivity)
  refine ⟨N, fun n hnN => ?_⟩
  have hlow : (∫ ξ in Metric.closedBall (0 : Space) R, F n ξ) < ε / 2 := by
    have hh := hN n hnN
    rw [Real.dist_eq, sub_zero] at hh
    exact lt_of_le_of_lt (le_abs_self _) hh
  have hnonneg : 0 ≤ ∫ ξ, F n ξ / (1 + 4 * Real.pi^2 * ‖ξ‖^2) :=
    integral_nonneg (fun ξ => div_nonneg (hn n ξ) (by positivity))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hnonneg]
  have hs := weighted_split_bound (hf n) (hn n) (hb n) hR
  linarith

theorem real_toLp_norm_sq {f : Space → ℝ} (hf : MemLp f 2 (volume : Measure Space)) :
    ‖hf.toLp f‖^2 = ∫ x, ‖f x‖^2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx, real_inner_self_eq_norm_sq]

theorem weighted_fourier_energy_tendsto_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ ξ, ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2 /
      (1 + 4 * Real.pi^2 * ‖ξ‖^2)) atTop (𝓝 0) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  have hi (n : ℕ) : Integrable (fun ξ => ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2) := by
    exact Burnett.Fourier.fourier_norm_sq_integrable
      (Burnett.Analysis.LocalHminusFourier.sourceSchwartz (hs n) χ (hχ n))
  have hb (n : ℕ) : (∫ ξ, ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2) ≤ B^2 := by
    calc
      _ = ∫ x, ‖(f n x : ℂ)‖^2 :=
        Burnett.Fourier.schwartz_parseval
          (Burnett.Analysis.LocalHminusFourier.sourceSchwartz (hs n) χ (hχ n))
      _ = ∫ x, ‖f n x‖^2 := by simp only [Complex.norm_real]
      _ = ‖(hf n).toLp (f n)‖^2 := (real_toLp_norm_sq (hf n)).symm
      _ ≤ B^2 := (sq_le_sq₀ (norm_nonneg _) hB0).mpr (hB n)
  apply weighted_energy_tendsto_zero hi (fun n ξ => sq_nonneg _) (sq_nonneg B) hb
  intro R
  exact Burnett.Analysis.LocalHminusFourier.low_frequency_energy_tendsto_zero hs hf χ hχ hB ht R

theorem weighted_fourier_norm_tendsto_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (∫ ξ, ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2 /
      (1 + 4 * Real.pi^2 * ‖ξ‖^2))) atTop (𝓝 0) := by
  simpa using (weighted_fourier_energy_tendsto_zero hs hf χ hχ hB ht).sqrt

end Burnett.Analysis.HminusWeightedTail
