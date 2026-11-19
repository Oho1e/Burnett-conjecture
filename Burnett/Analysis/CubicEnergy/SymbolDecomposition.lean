import Burnett.Analysis.CubicEnergy.LowSymbol
import Burnett.Analysis.CubicEnergy.HomogeneousBounds

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Set Burnett.RicciSymbol
open scoped ContDiff BigOperators

/-- The joint Cartesian derivative estimates for an order-zero bilinear multiplier symbol. -/
def CoifmanMeyerSymbol (f : E × E → ℝ) : Prop :=
  ContDiffOn ℝ ∞ f {p | p ≠ 0} ∧ ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ η ξ : E, (η,ξ) ≠ 0 → ‖iteratedFDeriv ℝ n f (η,ξ)‖*(‖η‖+‖ξ‖)^n ≤ C

/-- For a real, smooth degree-one symbol the three bilinear symbols have all
Cartesian order-zero bounds, the linear output factor has the corresponding
one-frequency bounds, and the four-dimensional splitting is an exact identity. -/
theorem commutator_symbol_decomposition (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hhom : ∀ t : ℝ, 0<t → ∀ z, b (t • z)=t*b z) :
    (∀ j : Index,
      CoifmanMeyerSymbol (fun p => lowSymbol b j p.1 p.2) ∧
      CoifmanMeyerSymbol (fun p => productSymbol j p.1 p.2) ∧
      CoifmanMeyerSymbol (fun p => inputSymbol j p.1 p.2) ∧
      (ContDiffOn ℝ ∞ (angularComponent b j) {x | x ≠ 0} ∧
        ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x : E, x ≠ 0 →
          ‖iteratedFDeriv ℝ n (angularComponent b j) x‖ * ‖x‖^n ≤ C)) ∧
    ∀ η ξ : E, b (η+ξ) - b ξ =
      (∑ j, η j * lowSymbol b j η ξ) +
      (∑ j, angularComponent b j (η+ξ) * productSymbol j η ξ * ‖η‖) -
      ∑ j, inputSymbol j η ξ * ‖η‖ * angularComponent b j ξ := by
  refine ⟨?_,commutator_symbol_eq b hb (homogeneous_value_zero hhom)⟩
  intro j
  have hlow := lowSymbol_contDiffOn b hb j
  have hprod := productSymbol_contDiffOn j
  have hin := inputSymbol_contDiffOn j
  have hout := angularComponent_contDiffOn b hb j
  exact ⟨⟨hlow,joint_derivative_bounds _ hlow (fun s hs p => lowSymbol_scale hb hhom j s hs p.1 p.2)⟩,
    ⟨hprod,joint_derivative_bounds _ hprod (fun s hs p => (highSymbols_scale j s hs p.1 p.2).1)⟩,
    ⟨hin,joint_derivative_bounds _ hin (fun s hs p => (highSymbols_scale j s hs p.1 p.2).2)⟩,
    hout,degreeZero_derivative_bounds _ hout (angularComponent_scale hhom j)⟩

end Burnett.A02.FrequencySplit
