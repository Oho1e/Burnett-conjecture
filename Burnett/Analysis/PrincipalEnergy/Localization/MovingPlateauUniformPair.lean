import Burnett.Analysis.PrincipalEnergy.Localization.UniformCompactMatrixPair
import Burnett.Analysis.PrincipalEnergy.Localization.FiniteMatrixNear

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff NNReal

theorem matrixSchwartzL2Norm_translate {κ : Type*} [Fintype κ] (c : Space)
    (f : κ → SchwartzMap Space ℂ) :
    matrixSchwartzL2Norm (fun j => translateSchwartz c (f j)) = matrixSchwartzL2Norm f := by
  have hp : 0 < (2 : ENNReal).toReal := by norm_num
  unfold matrixSchwartzL2Norm
  rw [PiLp.norm_eq_sum hp, PiLp.norm_eq_sum hp]
  simp only [PiLp.toLp_apply, translateSchwartz_L2_norm]

/-- The actual physical matrix pairing on every translate of the fixed
plateau has a single constant. Its original symbol is evaluated globally,
and the bounds on the coefficient and tests are in the original coordinates. -/
theorem exists_movingPlateauMatrix_uniform_physical_pair_bound {κ : Type*} [Fintype κ]
    {a : κ → κ → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (hχReal : ∀ x, conj (χ x) = χ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c : Space) (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : κ → SchwartzMap Space ℂ,
        (∀ j x, x ∈ tsupport (f j : Space → ℂ) → translateSchwartz (-c) χ x = 1) →
        (∀ i x, x ∈ tsupport (g i : Space → ℂ) → translateSchwartz (-c) χ x = 1) →
        ‖actualMatrixCommutatorPair a r f g‖ ≤
          C * (U + (L : ℝ)) * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
  let B (c : Space) (i j : κ) := movingPlateauSymbol (a i j) χ c
  have input (c : Space) := movingPlateauMatrix_compactBase_inputs ha hs hb hSym χ hχ hχReal c
  have family (i j : κ) : UniformCompactSymbolFamily (fun c => B c i j) := by
    refine ⟨movingPlateauSymbol_common_base_support (a i j) hχ,
      fun c => ((input c).1 i j).frequency.smooth,
      fun c => ((input c).2.1 i j).smooth,
      fun c => (input c).2.2.1 i j,
      fun c n => ((input c).1 i j).baseDiff n, ?_, ?_, ?_⟩
    · exact fun n => movingPlateauSymbol_uniform_frequencyOrder (ha i j).frequency χ n
    · exact (movingPlateauSymbol_uniform_pureBaseOrder (hs i j) (hb i j) χ).2
    · exact fun n => (movingPlateauSymbol_uniform_firstBaseFrequencyOrder (ha i j) (hs i j) χ n).2
  obtain ⟨C, hC, bound⟩ := exists_uniform_compactBase_matrix_coefficientCommutator_L2_pair_bound
    family (fun c => (input c).2.2.2)
  refine ⟨C, hC, fun c r L U hU hr hReal hVal hDer f g hf hg => ?_⟩
  let r' := translateSchwartz c r
  let f' (i : κ) := translateSchwartz c (f i)
  let g' (i : κ) := translateSchwartz c (g i)
  let Q := translateSchwartz (-c) χ
  let A (i j : κ) := cutoffSandwichSymbol (a i j) Q
  let τ : Space ≃ᵐ Space := MeasurableEquiv.addRight c
  have hτ : MeasurePreserving τ (volume : Measure Space) volume := measurePreserving_add_right volume c
  have hR : HasCompactSupport (r' : Space → ℂ) := hr.comp_homeomorph (Homeomorph.addRight c)
  have hReal' (x : Space) : conj (r' x) = r' x := hReal (x+c)
  have hVal' : ∀ᵐ x ∂(volume : Measure Space), ‖r' x‖ ≤ U := hτ.quasiMeasurePreserving.ae hVal
  have hDer' : ∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r' : Space → ℂ) x‖ ≤ (L:ℝ) := by
    filter_upwards [hτ.quasiMeasurePreserving.ae hDer] with x hx
    change ‖fderiv ℝ (translateSchwartz c r : Space → ℂ) x‖ ≤ (L:ℝ)
    rw [translateSchwartz_fderiv]
    exact hx
  have hSymbol (i j : κ) : B c i j = fun x => A i j (x+c) := by
    funext x ξ
    exact (cutoffSandwichSymbol_recenter (a i j) χ c x ξ).symm
  have hAction (i : κ) (x : Space) :
      matrixCoefficientCommutator (B c) r' f' i x = matrixCoefficientCommutator A r f i (x+c) := by
    simp only [matrixCoefficientCommutator_apply, hSymbol, r', f', actualCoefficientCommutator_translate]
  have hPair :
      actualMatrixCommutatorPair (B c) r' f' g' = actualMatrixCommutatorPair a r f g := by
    calc
      _ = actualMatrixCommutatorPair A r f g := by
        unfold actualMatrixCommutatorPair
        apply Finset.sum_congr rfl
        intro i _
        simp only [hAction, g', translateSchwartz_apply]
        exact hτ.integral_comp' (fun x => conj (g i x) * matrixCoefficientCommutator A r f i x)
      _ = _ := cutoffSandwich_matrix_coefficientCommutator_pair_eq
        (fun i j => (ha i j).frequency) Q r f g hf hg
  have h := bound c r' L U hU hR hReal' hVal' hDer' f' g'
  change ‖actualMatrixCommutatorPair (B c) r' f' g'‖ ≤
    C * (U + (L:ℝ)) * matrixSchwartzL2Norm f' * matrixSchwartzL2Norm g' at h
  simpa only [hPair, f', g', matrixSchwartzL2Norm_translate] using h

end Burnett.Analysis.CarlesonEmbedding
