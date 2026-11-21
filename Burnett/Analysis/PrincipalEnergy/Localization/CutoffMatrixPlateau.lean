import Burnett.Analysis.PrincipalEnergy.Localization.MatrixCommutatorBound
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffCommutatorPair

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate NNReal

theorem matrixFirstOrderAction_cutoffSandwich {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (χ : SchwartzMap Space ℂ) (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
    matrixFirstOrderAction (fun k l => cutoffSandwichSymbol (a k l) χ) f i x =
      χ x * matrixFirstOrderAction a (fun j => scalarSchwartzProduct χ (f j)) i x := by
  simp only [matrixFirstOrderAction, firstOrderAction_cutoffSandwichSymbol (ha _ _), Finset.mul_sum]

/-- A real cutoff on both sides of the actual matrix action preserves
the symmetry of the whole matrix pairing. -/
theorem cutoffSandwich_matrixFirstOrderFormalSymmetry {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (hs : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hχ : ∀ x, conj (χ x) = χ x) :
    MatrixFirstOrderFormalSymmetry (fun i j => cutoffSandwichSymbol (a i j) χ) := by
  intro f g
  let F (j : ι) := scalarSchwartzProduct χ (f j)
  let G (j : ι) := scalarSchwartzProduct χ (g j)
  calc
    _ = ∑ i, ∫ x, conj (G i x) * matrixFirstOrderAction a F i x := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      rw [matrixFirstOrderAction_cutoffSandwich ha]
      simp only [G, scalarSchwartzProduct_apply, map_mul, hχ]
      ring
    _ = ∑ i, ∫ x, conj (matrixFirstOrderAction a G i x) * F i x := hs F G
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      filter_upwards with x
      rw [matrixFirstOrderAction_cutoffSandwich ha]
      simp only [F, scalarSchwartzProduct_apply, map_mul, hχ]
      ring

/-- The actual finite matrix commutator tested with two fields supported in
the same fixed real plateau has exactly the original physical pairing. -/
theorem cutoffSandwich_matrix_coefficientCommutator_pair_eq {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (χ r : SchwartzMap Space ℂ) (f g : ι → SchwartzMap Space ℂ)
    (hf : ∀ j x, x ∈ tsupport (f j : Space → ℂ) → χ x = 1)
    (hg : ∀ i x, x ∈ tsupport (g i : Space → ℂ) → χ x = 1) :
    (∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator
      (fun j k => cutoffSandwichSymbol (a j k) χ) r f i x) =
      ∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator a r f i x := by
  have hfCut : (fun j => scalarSchwartzProduct χ (f j)) = f := by
    funext j
    ext x
    by_cases h : f j x = 0
    · simp only [scalarSchwartzProduct_apply, h, mul_zero]
    · rw [scalarSchwartzProduct_apply, hf j x (subset_closure h), one_mul]
  let rf (j : ι) := scalarSchwartzProduct r (f j)
  have hrCut : (fun j => scalarSchwartzProduct χ (rf j)) = rf := by
    funext j
    ext x
    by_cases h : f j x = 0
    · simp only [rf, scalarSchwartzProduct_apply, h, mul_zero]
    · rw [scalarSchwartzProduct_apply, hf j x (subset_closure h), one_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards with x
  by_cases h : g i x = 0
  · simp only [h, map_zero, zero_mul]
  · simp only [matrixCoefficientCommutator, matrixFirstOrderAction_cutoffSandwich ha, hg i x (subset_closure h),
      one_mul, hfCut]
    change conj (g i x) *
        (r x * matrixFirstOrderAction a f i x -
          matrixFirstOrderAction a (fun j => scalarSchwartzProduct χ (rf j)) i x) = _
    rw [hrCut]

/-- The fixed-plateau reduction of the original matrix pairing. The
compact-base and mixed seminorm hypotheses refer to the exact sandwich
symbol, so they are available to the same scalar Calderón bound. -/
theorem exists_matrix_coefficientCommutator_L2_pair_bound_on_plateau {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (hSym : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hRealχ : ∀ x, conj (χ x) = χ x)
    (hMixed : ∀ i j, FirstBaseFrequencyOrderOne (cutoffSandwichSymbol (a i j) χ))
    (hCompact : ∀ i j, CompactBaseOrderOne (cutoffSandwichSymbol (a i j) χ))
    (hCont : ∀ i j, Continuous (uncurry (cutoffSandwichSymbol (a i j) χ))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : ι → SchwartzMap Space ℂ,
        (∀ j x, x ∈ tsupport (f j : Space → ℂ) → χ x = 1) →
        (∀ i x, x ∈ tsupport (g i : Space → ℂ) → χ x = 1) →
        ‖∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator a r f i x‖ ≤
          C * (U + (L : ℝ)) * ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖ *
            ‖WithLp.toLp 2 (fun i => (g i).toLp 2 volume)‖ := by
  obtain ⟨C, hC, bound⟩ := exists_compactBase_matrix_coefficientCommutator_L2_pair_bound
    hMixed hCompact hCont (cutoffSandwich_matrixFirstOrderFormalSymmetry ha hSym χ hRealχ)
  refine ⟨C, hC, fun r L U hU hr hR hValue hDeriv f g hf hg => ?_⟩
  rw [← cutoffSandwich_matrix_coefficientCommutator_pair_eq ha χ r f g hf hg]
  exact bound r L U hU hr hR hValue hDeriv f g

end Burnett.Analysis.CarlesonEmbedding
