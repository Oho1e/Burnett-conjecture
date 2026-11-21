import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauCovariance
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichMixedIntegrand

set_option autoImplicit false
set_option maxHeartbeats 3600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform

/-- One original coefficient is sampled at every center before applying the
same two-sided Schwartz cutoff. -/
def movingPlateauSymbol (a : Space → Space → ℂ) (χ : SchwartzMap Space ℂ)
    (c : Space) : Space → Space → ℂ :=
  cutoffSandwichSymbol (fun x => a (x + c)) χ

theorem frequencyOrderOne_translate_base {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (c : Space) :
    FrequencyOrderOne (fun x => a (x + c)) := by
  refine ⟨fun x => ha.smooth (x + c), fun n => ?_⟩
  obtain ⟨C, hC, hb⟩ := ha.order n
  exact ⟨C, hC, fun x ξ => hb (x + c) ξ⟩

/-- Base translation preserves joint smoothness. -/
theorem contDiff_symbol_translate_base {a : Space → Space → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (c : Space) :
    ContDiff ℝ ∞ (uncurry (fun x => a (x + c))) :=
  ha.comp ((contDiff_fst.add contDiff_const).prodMk contDiff_snd)

/-- A single constant for the frequency order is selected before any center,
base point, or frequency is given. -/
theorem movingPlateauSymbol_uniform_frequencyOrder {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (χ : SchwartzMap Space ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c x ξ,
      ‖iteratedFDeriv ℝ n (movingPlateauSymbol a χ c x) ξ‖ * (1 + ‖ξ‖)^n ≤
        C * (1 + ‖ξ‖) := by
  obtain ⟨M, hM, order⟩ := ha.order n
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let S := SchwartzMap.seminorm ℝ 0 0 χ
  let w (η : Space) := (1 + ‖η‖)^(n + 1) * ‖F η‖
  have hW : Integrable w (volume : Measure Space) := integrable_schwartz_weighted F (n + 1)
  have hS : 0 ≤ S := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ χ (0 : Space))
  have hI : 0 ≤ ∫ η, w η := integral_nonneg (fun η => by dsimp [w]; positivity)
  refine ⟨S * M * (∫ η, w η), by positivity, fun c x ξ => ?_⟩
  have hz := (cutoffSandwichSymbol_frequency_jets (frequencyOrderOne_translate_base ha c) χ x).2 n ξ
  unfold movingPlateauSymbol
  rw [hz]
  let G (η : Space) := sandwichFrequencyFactor χ x η • iteratedFDeriv ℝ n (a (x + c)) (ξ + η)
  let W := (1 + ‖ξ‖)^n
  have hW₀ : 0 ≤ W := by dsimp [W]; positivity
  change ‖∫ η, G η‖ * W ≤ _
  calc
    _ = ‖W • (∫ η, G η)‖ := by rw [norm_smul, Real.norm_of_nonneg hW₀, mul_comm]
    _ = ‖∫ η, W • G η‖ := by rw [integral_smul]
    _ ≤ ∫ η, (S * M * (1 + ‖ξ‖)) * w η := by
      apply norm_integral_le_of_norm_le (hW.const_mul _)
      filter_upwards with η
      have hPhase : ‖sandwichFrequencyFactor χ x η‖ ≤ S * ‖F η‖ :=
        (sandwichFrequencyFactor_base_controls χ x η).1
      have hJet := shifted_frequency_order_weight_le (fun y ζ => iteratedFDeriv ℝ n (a y) ζ)
        n hM order (x + c) ξ η
      rw [norm_smul, Real.norm_of_nonneg hW₀, mul_comm]
      simp only [G, norm_smul, mul_assoc, W]
      exact (mul_le_mul hPhase hJet (by positivity) (mul_nonneg hS (norm_nonneg _))).trans_eq
        (by dsimp only [w]; ring)
    _ = _ := by rw [integral_const_mul]; ring

/-- The centered bases of all the sandwiches are supported in one compact set. -/
theorem movingPlateauSymbol_common_base_support (a : Space → Space → ℂ)
    {χ : SchwartzMap Space ℂ} (hχ : HasCompactSupport (χ : Space → ℂ)) :
    ∃ K : Set Space, IsCompact K ∧ ∀ c ξ, tsupport (fun x => movingPlateauSymbol a χ c x ξ) ⊆ K := by
  exact ⟨tsupport (χ : Space → ℂ), hχ, fun c ξ =>
    cutoffSandwichSymbol_base_support (a := fun x => a (x + c)) χ ξ⟩

end Burnett.Analysis.CarlesonEmbedding
