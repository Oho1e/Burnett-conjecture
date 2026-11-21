import Burnett.Analysis.PrincipalEnergy.Localization.CutoffMatrixPlateau
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichPureBase
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichMixed

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators NNReal ContDiff ComplexConjugate

/-- For one fixed real compact plateau, the physical matrix commutator
bound follows from the original order-one symbol assumptions. -/
theorem exists_matrix_coefficientCommutator_L2_pair_bound_for_fixed_cutoff {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ}
    (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hSmooth : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hPure : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a) (χ : SchwartzMap Space ℂ)
    (hχ : HasCompactSupport (χ : Space → ℂ)) (hRealχ : ∀ x, conj (χ x) = χ x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : ι → SchwartzMap Space ℂ,
        (∀ j x, x ∈ tsupport (f j : Space → ℂ) → χ x = 1) →
        (∀ i x, x ∈ tsupport (g i : Space → ℂ) → χ x = 1) →
        ‖∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator a r f i x‖ ≤
          C * (U + (L : ℝ)) * ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖ *
            ‖WithLp.toLp 2 (fun i => (g i).toLp 2 volume)‖ :=
  exists_matrix_coefficientCommutator_L2_pair_bound_on_plateau
    (fun i j => (ha i j).frequency) hSym χ hRealχ
    (fun i j => cutoffSandwichSymbol_firstBaseFrequencyOrderOne (ha i j) (hSmooth i j) χ)
    (fun i j => cutoffSandwichSymbol_compactBaseOrderOne (hSmooth i j) (hPure i j) χ hχ)
    (fun i j => cutoffSandwichSymbol_jointContinuous (hSmooth i j) (hPure i j) χ)

end Burnett.Analysis.CarlesonEmbedding
