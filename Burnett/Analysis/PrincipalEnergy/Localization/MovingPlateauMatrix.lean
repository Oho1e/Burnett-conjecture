import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauMixed
import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauPureBase
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffMatrixPlateau
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichPureBase
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichMixed

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff NNReal

theorem matrixFirstOrderFormalSymmetry_translate_base {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : MatrixFirstOrderFormalSymmetry a) (c : Space) :
    MatrixFirstOrderFormalSymmetry (fun i j x => a i j (x+c)) := by
  intro f g
  let pull (u : ι → SchwartzMap Space ℂ) (j : ι) := translateSchwartz (-c) (u j)
  have hId (u : ι → SchwartzMap Space ℂ) (j : ι) :
      translateSchwartz c (pull u j) = u j := by
    ext x
    simp only [pull, translateSchwartz_apply, add_neg_cancel_right]
  have hVal (u : ι → SchwartzMap Space ℂ) (j : ι) (x : Space) : pull u j (x+c) = u j x := by
    simp only [pull, translateSchwartz_apply, add_neg_cancel_right]
  have hAction (u : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
      matrixFirstOrderAction (fun i j z => a i j (z+c)) u i x =
        matrixFirstOrderAction a (pull u) i (x+c) := by
    apply Finset.sum_congr rfl
    intro j _
    have h := firstOrderAction_translate (a i j) c (pull u j) x
    rwa [hId] at h
  let τ : Space ≃ᵐ Space := MeasurableEquiv.addRight c
  have hτ : MeasurePreserving τ (volume : Measure Space) volume := measurePreserving_add_right volume c
  calc
    _ = ∑ i, ∫ x, conj (pull g i (τ x)) * matrixFirstOrderAction a (pull f) i (τ x) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hAction, show ∀ x, τ x = x+c from fun _ => rfl, hVal]
    _ = ∑ i, ∫ x, conj (pull g i x) * matrixFirstOrderAction a (pull f) i x := by
      apply Finset.sum_congr rfl
      intro i _
      exact hτ.integral_comp' (fun x => conj (pull g i x) * matrixFirstOrderAction a (pull f) i x)
    _ = ∑ i, ∫ x, conj (matrixFirstOrderAction a (pull g) i x) * pull f i x := ha (pull f) (pull g)
    _ = ∑ i, ∫ x, conj (matrixFirstOrderAction a (pull g) i (τ x)) * pull f i (τ x) := by
      apply Finset.sum_congr rfl
      intro i _
      exact (hτ.integral_comp' (fun x => conj (matrixFirstOrderAction a (pull g) i x) * pull f i x)).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [hAction, show ∀ x, τ x = x+c from fun _ => rfl, hVal]

/-- Every center supplies the actual compact-base matrix inputs to the
local pairing theorem. The separate shared seminorms retain their stronger
quantifier order. -/
theorem movingPlateauMatrix_compactBase_inputs {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (hχReal : ∀ x, conj (χ x) = χ x) (c : Space) :
    let b := fun i j => movingPlateauSymbol (a i j) χ c
    (∀ i j, FirstBaseFrequencyOrderOne (b i j)) ∧
    (∀ i j, CompactBaseOrderOne (b i j)) ∧
    (∀ i j, Continuous (uncurry (b i j))) ∧ MatrixFirstOrderFormalSymmetry b := by
  intro b
  have hPure' (i j : ι) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j (y+c) ξ) x‖ ≤ C * (1 + ‖ξ‖) := by
    obtain ⟨C, hC, h⟩ := hb i j n
    refine ⟨C, hC, fun x ξ => ?_⟩
    rw [iteratedFDeriv_comp_add_right (f := fun y => a i j y ξ) n c x]
    exact h (x+c) ξ
  refine ⟨fun i j => ?_, fun i j => ?_, fun i j => ?_, ?_⟩
  · exact cutoffSandwichSymbol_firstBaseFrequencyOrderOne (firstBaseFrequencyOrderOne_translate_base (ha i j) c)
      (contDiff_symbol_translate_base (hs i j) c) χ
  · exact cutoffSandwichSymbol_compactBaseOrderOne (contDiff_symbol_translate_base (hs i j) c) (hPure' i j) χ hχ
  · exact cutoffSandwichSymbol_jointContinuous (contDiff_symbol_translate_base (hs i j) c) (hPure' i j) χ
  · exact cutoffSandwich_matrixFirstOrderFormalSymmetry
      (fun i j => frequencyOrderOne_translate_base (ha i j).frequency c)
      (matrixFirstOrderFormalSymmetry_translate_base hSym c) χ hχReal

/-- The actual moving sandwich has the local L² pairing estimate at an
arbitrary specified center. -/
theorem exists_movingPlateauMatrix_L2_pair_bound_at_center {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (hχReal : ∀ x, conj (χ x) = χ x) (c : Space) :
    let b := fun i j => movingPlateauSymbol (a i j) χ c
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : ι → SchwartzMap Space ℂ,
        ‖∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator b r f i x‖ ≤
          C * (U + (L : ℝ)) * ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖ *
            ‖WithLp.toLp 2 (fun i => (g i).toLp 2 volume)‖ := by
  intro b
  obtain ⟨hM, hB, hC, hS⟩ := movingPlateauMatrix_compactBase_inputs ha hs hb hSym χ hχ hχReal c
  exact exists_compactBase_matrix_coefficientCommutator_L2_pair_bound hM hB hC hS

end Burnett.Analysis.CarlesonEmbedding
