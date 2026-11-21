import Burnett.Analysis.PrincipalEnergy.Localization.UniformCompactH1Pair

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic Burnett.Analysis.SymmetricEnergy
open scoped BigOperators ComplexConjugate ContDiff

theorem coordinateH1_translate (c : Space) (f : SchwartzMap Space ℂ) :
    coordinateH1 (translateSchwartz c f) = coordinateH1 f := by
  have hD (b : Fin 4) : SchwartzMap.pderivCLM ℂ (coordinateDirection b) (translateSchwartz c f) =
      translateSchwartz c (SchwartzMap.pderivCLM ℂ (coordinateDirection b) f) := by
    ext x
    simp only [SchwartzMap.pderivCLM_apply, translateSchwartz_fderiv, translateSchwartz_apply]
  simp only [coordinateH1, hD, translateSchwartz_L2_norm]

theorem movingPlateauSymbol_uniformCompactFamily {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)) :
    UniformCompactSymbolFamily (movingPlateauSymbol a χ) := by
  obtain ⟨hSmoothBase, base⟩ := movingPlateauSymbol_uniform_pureBaseOrder hs hb χ
  refine ⟨movingPlateauSymbol_common_base_support a hχ,
    fun c x => (cutoffSandwichSymbol_frequency_jets (frequencyOrderOne_translate_base ha.frequency c) χ x).1,
    hSmoothBase, ?_, fun c n ξ =>
      (movingPlateauSymbol_uniform_firstBaseFrequencyOrder ha hs χ n).1 c ξ,
    movingPlateauSymbol_uniform_frequencyOrder ha.frequency χ, base,
    fun n => (movingPlateauSymbol_uniform_firstBaseFrequencyOrder ha hs χ n).2⟩
  intro c
  apply cutoffSandwichSymbol_jointContinuous (contDiff_symbol_translate_base hs c) _ χ
  intro n
  obtain ⟨C, hC, hBound⟩ := hb n
  refine ⟨C, hC, fun x ξ => ?_⟩
  rw [iteratedFDeriv_comp_add_right (f := fun y => a y ξ) n c x]
  exact hBound (x+c) ξ

/-- Uniform compact-base H¹ bound after the exact physical recentering,
for inputs and tests in the one part of each moving plateau. -/
theorem exists_movingPlateau_h1_physical_pair_bound {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Space) (f g : SchwartzMap Space ℂ),
      (∀ x ∈ tsupport (f : Space → ℂ), translateSchwartz (-c) χ x = 1) →
      (∀ x ∈ tsupport (g : Space → ℂ), translateSchwartz (-c) χ x = 1) →
      ‖∫ x, conj (g x) * firstOrderAction a f x‖ ≤ C * coordinateH1 f * ‖g.toLp 2 volume‖ := by
  obtain ⟨C, hC, bound⟩ := exists_uniformCompactSymbolFamily_h1_pair_bound
    (movingPlateauSymbol_uniformCompactFamily ha hs hb χ hχ)
  refine ⟨C, hC, fun c f g hf hg => ?_⟩
  let Q := translateSchwartz (-c) χ
  have hF : scalarSchwartzProduct Q f = f := by
    ext x
    by_cases hx : f x = 0
    · simp only [scalarSchwartzProduct_apply, hx, mul_zero]
    · rw [scalarSchwartzProduct_apply, hf x (subset_closure hx), one_mul]
  let τ : Space ≃ᵐ Space := MeasurableEquiv.addRight c
  have hτ : MeasurePreserving τ (volume : Measure Space) volume := measurePreserving_add_right volume c
  have hEq :
      (∫ x, conj (translateSchwartz c g x) *
        firstOrderAction (movingPlateauSymbol a χ c) (translateSchwartz c f) x) =
        ∫ x, conj (g x) * firstOrderAction a f x := by
    calc
      _ = ∫ x, conj (g (τ x)) * firstOrderAction a f (τ x) := by
        apply integral_congr_ae
        filter_upwards with x
        change conj (g (x+c)) * firstOrderAction (cutoffSandwichSymbol (fun y => a (y+c)) χ)
          (translateSchwartz c f) x = conj (g (x+c)) * firstOrderAction a f (x+c)
        rw [firstOrderAction_movingPlateau a ha.frequency]
        change conj (g (x+c)) * (Q (x+c) * firstOrderAction a (scalarSchwartzProduct Q f) (x+c)) = _
        rw [hF]
        by_cases hx : g (x+c) = 0
        · simp only [hx, map_zero, zero_mul]
        · rw [hg _ (subset_closure hx), one_mul]
      _ = _ := hτ.integral_comp' (fun x => conj (g x) * firstOrderAction a f x)
  simpa only [hEq, coordinateH1_translate, translateSchwartz_L2_norm] using
    bound c (translateSchwartz c f) (translateSchwartz c g)

end Burnett.Analysis.CarlesonEmbedding
