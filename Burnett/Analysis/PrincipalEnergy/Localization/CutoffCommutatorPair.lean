import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichSymbol

set_option autoImplicit false
set_option maxHeartbeats 3200000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ComplexConjugate

/-- The exact physical commutator pairing between tests in a fixed plateau
is preserved by the actual two-sided cutoff of the symbol. -/
theorem cutoffSandwich_commutator_pair_eq
    {a : Space → Space → ℂ} (ha : FrequencyOrderOne a)
    (χ r f g : SchwartzMap Space ℂ)
    (hχf : ∀ x ∈ tsupport (f : Space → ℂ), χ x=1)
    (hχg : ∀ x ∈ tsupport (g : Space → ℂ), χ x=1) :
    (∫ x, conj (g x)*actualCoefficientCommutator (cutoffSandwichSymbol a χ) r f x)=
      ∫ x, conj (g x)*actualCoefficientCommutator a r f x := by
  have hF : scalarSchwartzProduct χ f=f := by
    ext x
    by_cases hx : f x=0
    · simp only [scalarSchwartzProduct_apply,hx,mul_zero]
    · rw [scalarSchwartzProduct_apply,hχf x (subset_closure hx),one_mul]
  have hR : scalarSchwartzProduct χ (scalarSchwartzProduct r f)=scalarSchwartzProduct r f := by
    ext x
    by_cases hx : f x=0
    · simp only [scalarSchwartzProduct_apply,hx,mul_zero]
    · rw [scalarSchwartzProduct_apply,hχf x (subset_closure hx),one_mul]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : g x=0
  · simp only [hx,map_zero,zero_mul]
  · simp only [actualCoefficientCommutator,firstOrderAction_cutoffSandwichSymbol ha,
      hχg x (subset_closure hx),one_mul,hF,hR]

/-- The compact left cutoff supplies a common base support for every
frequency of the actual sandwich symbol. -/
theorem cutoffSandwichSymbol_hasCompactBase
    (a : Space → Space → ℂ) (χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)) :
    ∃ K : Set Space, IsCompact K ∧ ∀ ξ, tsupport (fun x => cutoffSandwichSymbol a χ x ξ) ⊆ K :=
  ⟨tsupport (χ : Space → ℂ),hχ,cutoffSandwichSymbol_base_support χ⟩

end Burnett.Analysis.CarlesonEmbedding
