import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichSymbol
import Burnett.Analysis.PrincipalEnergy.Localization.IntegratedSymbolJets

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Metric Filter Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform

private theorem one_add_norm_add_le (ξ η : Space) :
    1 + ‖ξ + η‖ ≤ (1 + ‖ξ‖) * (1 + ‖η‖) := by
  nlinarith only [norm_add_le ξ η, mul_nonneg (norm_nonneg ξ) (norm_nonneg η)]

/-- Shifting the frequency retains the original order-one weight, with a
polynomial factor in the shift. This applies to either frequency or mixed jets. -/
theorem shifted_frequency_order_weight_le {F : Type*} [SeminormedAddCommGroup F]
    (J : Space → Space → F) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hOrder : ∀ x ξ, ‖J x ξ‖ * (1 + ‖ξ‖)^n ≤ M * (1 + ‖ξ‖))
    (x ξ η : Space) :
    ‖J x (ξ + η)‖ * (1 + ‖ξ‖)^n ≤
      M * (1 + ‖ξ‖) * (1 + ‖η‖)^(n + 1) := by
  have back : 1 + ‖ξ‖ ≤ (1 + ‖ξ + η‖) * (1 + ‖η‖) := by
    simpa only [add_assoc, add_neg_cancel, add_zero, norm_neg] using one_add_norm_add_le (ξ + η) (-η)
  calc
    _ ≤ ‖J x (ξ + η)‖ * ((1 + ‖ξ + η‖) * (1 + ‖η‖))^n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) back n) (norm_nonneg _)
    _ = (‖J x (ξ + η)‖ * (1 + ‖ξ + η‖)^n) * (1 + ‖η‖)^n := by
      rw [mul_pow]
      ring
    _ ≤ (M * (1 + ‖ξ + η‖)) * (1 + ‖η‖)^n :=
      mul_le_mul_of_nonneg_right (hOrder x (ξ + η)) (by positivity)
    _ ≤ (M * ((1 + ‖ξ‖) * (1 + ‖η‖))) * (1 + ‖η‖)^n :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (one_add_norm_add_le ξ η) hM) (by positivity)
    _ = _ := by rw [pow_succ]; ring

/-- Every polynomial weight of a Schwartz Fourier profile is integrable. -/
theorem integrable_schwartz_weighted (F : SchwartzMap Space ℂ) (n : ℕ) :
    Integrable (fun η => (1 + ‖η‖)^n * ‖F η‖) (volume : Measure Space) := by
  have base := (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure Space) n)).const_mul ((2 : ℝ)^n)
  have meas : Continuous (fun η : Space => (1 + ‖η‖)^n * ‖F η‖) :=
    ((continuous_const.add continuous_norm).pow n).mul F.continuous.norm
  refine base.mono' meas.aestronglyMeasurable (Eventually.of_forall fun η => ?_)
  change ‖(1 + ‖η‖)^n * ‖F η‖‖ ≤ 2^n * (‖F η‖ + ‖η‖^n * ‖F η‖)
  have hMax : 1 + ‖η‖ ≤ (2 : ℝ) * max 1 ‖η‖ := by
    nlinarith only [le_max_left 1 ‖η‖, le_max_right 1 ‖η‖]
  have hp : (max 1 ‖η‖)^n ≤ 1 + ‖η‖^n := by
    rcases le_total ‖η‖ 1 with h | h
    · rw [max_eq_left h, one_pow]
      exact le_add_of_nonneg_right (by positivity)
    · rw [max_eq_right h]
      exact le_add_of_nonneg_left zero_le_one
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (2 * max 1 ‖η‖)^n * ‖F η‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hMax n) (norm_nonneg _)
    _ ≤ (2^n * (1 + ‖η‖^n)) * ‖F η‖ := by
      rw [mul_pow]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (norm_nonneg _)
    _ = _ := by ring

/-- The two cutoff factors and the true frequency-translation phase. -/
def sandwichFrequencyFactor (χ : SchwartzMap Space ℂ) (x η : Space) : ℂ :=
  χ x * (Real.fourierChar (inner ℝ η x) : ℂ) * 𝓕 (χ : Space → ℂ) η

private theorem sandwichFrequencyFactor_norm (χ : SchwartzMap Space ℂ) (x η : Space) :
    ‖sandwichFrequencyFactor χ x η‖ = ‖χ x‖ * ‖𝓕 (χ : Space → ℂ) η‖ := by
  rw [sandwichFrequencyFactor, norm_mul, norm_mul, Circle.norm_coe, mul_one]

private theorem sandwichFrequencyFactor_continuous (χ : SchwartzMap Space ℂ) (x : Space) :
    Continuous (sandwichFrequencyFactor χ x) := by
  have phase : Continuous (fun η : Space => (Real.fourierChar (inner ℝ η x) : ℂ)) :=
    continuous_subtype_val.comp (Real.continuous_fourierChar.comp (continuous_id.inner continuous_const))
  exact (continuous_const.mul phase).mul (SchwartzMap.fourierTransformCLM ℂ χ).continuous

private theorem cutoffSandwichSymbol_integral (a : Space → Space → ℂ) (χ : SchwartzMap Space ℂ) (x : Space) :
    cutoffSandwichSymbol a χ x = fun ξ => ∫ η, sandwichFrequencyFactor χ x η • a x (ξ + η) := by
  funext ξ
  rw [cutoffSandwichSymbol, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with η
  simp only [sandwichFrequencyFactor, Circle.smul_def, smul_eq_mul]
  ring

private theorem sandwichIntegrand_iteratedFrequency {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (χ : SchwartzMap Space ℂ) (x η ξ : Space) (n : ℕ) :
    iteratedFDeriv ℝ n (fun z => sandwichFrequencyFactor χ x η • a x (z + η)) ξ =
      sandwichFrequencyFactor χ x η • iteratedFDeriv ℝ n (a x) (ξ + η) := by
  have hs : ContDiff ℝ ∞ (fun z : Space => a x (z + η)) :=
    (ha.smooth x).comp (contDiff_id.add contDiff_const)
  rw [iteratedFDeriv_const_smul_apply' (hs.contDiffAt.of_le (by exact_mod_cast le_top)),
    iteratedFDeriv_comp_add_right]

private theorem sandwichIntegrand_weighted_bound {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (χ : SchwartzMap Space ℂ) (x η ξ : Space) (n : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hOrder : ∀ y ζ, ‖iteratedFDeriv ℝ n (a y) ζ‖ * (1 + ‖ζ‖)^n ≤ M * (1 + ‖ζ‖)) :
    ‖iteratedFDeriv ℝ n (fun z => sandwichFrequencyFactor χ x η • a x (z + η)) ξ‖ *
      (1 + ‖ξ‖)^n ≤ (‖χ x‖ * M * (1 + ‖ξ‖)) * ((1 + ‖η‖)^(n + 1) * ‖𝓕 (χ : Space → ℂ) η‖) := by
  rw [sandwichIntegrand_iteratedFrequency ha, norm_smul, sandwichFrequencyFactor_norm]
  calc
    _ = (‖χ x‖ * ‖𝓕 (χ : Space → ℂ) η‖) *
        (‖iteratedFDeriv ℝ n (a x) (ξ + η)‖ * (1 + ‖ξ‖)^n) := by ring
    _ ≤ (‖χ x‖ * ‖𝓕 (χ : Space → ℂ) η‖) * (M * (1 + ‖ξ‖) * (1 + ‖η‖)^(n + 1)) :=
      mul_le_mul_of_nonneg_left (shifted_frequency_order_weight_le
        (fun y ζ => iteratedFDeriv ℝ n (a y) ζ) n hM hOrder x ξ η) (by positivity)
    _ = _ := by ring

/-- Differentiation in frequency takes place inside the genuine sandwich integral. -/
theorem cutoffSandwichSymbol_frequency_jets {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (χ : SchwartzMap Space ℂ) (x : Space) :
    ContDiff ℝ ∞ (cutoffSandwichSymbol a χ x) ∧ ∀ (n : ℕ) ξ,
      iteratedFDeriv ℝ n (cutoffSandwichSymbol a χ x) ξ =
        ∫ η, sandwichFrequencyFactor χ x η • iteratedFDeriv ℝ n (a x) (ξ + η) := by
  let u (η ξ : Space) := sandwichFrequencyFactor χ x η • a x (ξ + η)
  have hSmooth (η : Space) : ContDiff ℝ ∞ (u η) :=
    ((ha.smooth x).comp (contDiff_id.add contDiff_const)).const_smul _
  have hMeas (n : ℕ) (ξ : Space) :
      AEStronglyMeasurable (fun η => iteratedFDeriv ℝ n (u η) ξ) (volume : Measure Space) := by
    letI : NormedSpace ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
      ContinuousMultilinearMap.normedSpace'
    letI : ContinuousSMul ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
      IsBoundedSMul.continuousSMul
    have hJet : Continuous (fun η : Space => iteratedFDeriv ℝ n (a x) (ξ + η)) :=
      ((ha.smooth x).continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).comp
        (continuous_const.add continuous_id)
    simp only [u, sandwichIntegrand_iteratedFrequency ha]
    exact ((sandwichFrequencyFactor_continuous χ x).smul hJet).aestronglyMeasurable
  have hDom (n : ℕ) (ξ : Space) : ∃ B : Space → ℝ, Integrable B (volume : Measure Space) ∧
      ∀ η ζ, ζ ∈ ball ξ 1 → ‖iteratedFDeriv ℝ n (u η) ζ‖ ≤ B η := by
    obtain ⟨M, hM, hOrder⟩ := ha.order n
    let F := SchwartzMap.fourierTransformCLM ℂ χ
    refine ⟨fun η => (‖χ x‖ * M * (2 + ‖ξ‖)) * ((1 + ‖η‖)^(n + 1) * ‖F η‖),
      (integrable_schwartz_weighted F (n + 1)).const_mul _, fun η ζ hζ => ?_⟩
    have hd : ‖ζ - ξ‖ < 1 := by simpa only [mem_ball, dist_eq_norm] using hζ
    have hz : ‖ζ‖ ≤ 1 + ‖ξ‖ :=
      (by simpa only [sub_add_cancel] using norm_add_le (ζ - ξ) ξ :
        ‖ζ‖ ≤ ‖ζ - ξ‖ + ‖ξ‖).trans (add_le_add_right hd.le _)
    calc
      _ = ‖iteratedFDeriv ℝ n (u η) ζ‖ * 1 := (mul_one _).symm
      _ ≤ ‖iteratedFDeriv ℝ n (u η) ζ‖ * (1 + ‖ζ‖)^n :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg ζ))) (norm_nonneg _)
      _ ≤ (‖χ x‖ * M * (1 + ‖ζ‖)) * ((1 + ‖η‖)^(n + 1) * ‖F η‖) :=
        sandwichIntegrand_weighted_bound ha χ x η ζ n hM hOrder
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (by linarith only [hz]) (mul_nonneg (norm_nonneg _) hM)) (by positivity)
  rw [cutoffSandwichSymbol_integral]
  obtain ⟨hs, hJet⟩ := contDiff_integral_of_locally_dominated_jets
    (volume : Measure Space) u hSmooth hMeas hDom
  exact ⟨hs, fun n ξ => (hJet n ξ).trans (integral_congr_ae
    (Eventually.of_forall fun η => sandwichIntegrand_iteratedFrequency ha χ x η ξ n))⟩

/-- The actual two-sided cutoff retains every order-one normalized frequency
seminorm. At order n the same original seminorm and one Schwartz moment of
the actual cutoff Fourier transform control the new constant. -/
theorem cutoffSandwichSymbol_frequencyOrderOne {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (χ : SchwartzMap Space ℂ) : FrequencyOrderOne (cutoffSandwichSymbol a χ) := by
  refine ⟨fun x => (cutoffSandwichSymbol_frequency_jets ha χ x).1, ?_⟩
  intro n
  obtain ⟨M, hM, hOrder⟩ := ha.order n
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let w (η : Space) := (1 + ‖η‖)^(n + 1) * ‖F η‖
  let S := SchwartzMap.seminorm ℝ 0 0 χ
  have hW : Integrable w (volume : Measure Space) := integrable_schwartz_weighted F (n + 1)
  have hIW : 0 ≤ ∫ η, w η := integral_nonneg (fun η => by dsimp only [w]; positivity)
  have hS : 0 ≤ S := le_trans (norm_nonneg _) (SchwartzMap.norm_le_seminorm ℝ χ (0 : Space))
  refine ⟨S * M * (∫ η, w η), by positivity, fun x ξ => ?_⟩
  rw [(cutoffSandwichSymbol_frequency_jets ha χ x).2]
  let G (η : Space) := sandwichFrequencyFactor χ x η • iteratedFDeriv ℝ n (a x) (ξ + η)
  let W := (1 + ‖ξ‖)^n
  have hW₀ : 0 ≤ W := by dsimp only [W]; positivity
  change ‖∫ η, G η‖ * W ≤ _
  calc
    _ = ‖W • (∫ η, G η)‖ := by rw [norm_smul, Real.norm_of_nonneg hW₀, mul_comm]
    _ = ‖∫ η, W • G η‖ := by rw [integral_smul]
    _ ≤ ∫ η, (‖χ x‖ * M * (1 + ‖ξ‖)) * w η := by
      apply norm_integral_le_of_norm_le (hW.const_mul _)
      filter_upwards with η
      rw [norm_smul, Real.norm_of_nonneg hW₀, mul_comm]
      simpa only [G, W, w, F, sandwichIntegrand_iteratedFrequency ha] using
        sandwichIntegrand_weighted_bound ha χ x η ξ n hM hOrder
    _ = (‖χ x‖ * M * (∫ η, w η)) * (1 + ‖ξ‖) := by rw [integral_const_mul]; ring
    _ ≤ _ := by
      gcongr
      exact SchwartzMap.norm_le_seminorm ℝ χ x

end Burnett.Analysis.CarlesonEmbedding
