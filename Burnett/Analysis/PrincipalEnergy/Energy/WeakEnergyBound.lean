import Burnett.Analysis.PrincipalEnergy.Energy.SymmetricEnergy
import Mathlib.Tactic.Positivity

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsSkew (D : Op H) : Prop := ∀ u v, ⟪D u, v⟫_ℂ = -⟪u, D v⟫_ℂ

theorem derivative_commutator_symmetric (D B : Op H) (hD : IsSkew D) (hB : B.IsSymmetric) :
    (comm D B).IsSymmetric := by
  intro x y
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, inner_sub_left, inner_sub_right]
  rw [hD, hB, hB, hD]
  ring

/-- After the adjoint moves the three pairings involve only one derivative
on either copy of the test, or one of the two first-order commutators. -/
theorem weak_divergence_commutator (D R E B : Op H) (hD : IsSkew D) (hB : B.IsSymmetric) (u : H) :
    ⟪u, comm (-(D * R * E)) B u⟫_ℂ =
      ⟪D u, R (comm E B u)⟫_ℂ + ⟪D u, comm R B (E u)⟫_ℂ -
      ⟪comm D B u, R (E u)⟫_ℂ := by
  rw [divergence_commutator_term]
  simp only [LinearMap.sub_apply, LinearMap.neg_apply, Module.End.mul_apply, inner_neg_right, inner_sub_right]
  rw [hD, hD, (derivative_commutator_symmetric D B hD hB) u (R (E u))]
  ring

/-- Per indexed summand, a multiplication bound A, first-order commutator
bound C and Lipschitz commutator bound L control the pairing by
(2 A C + L) times the square of the test's energy. -/
theorem weak_commutator_bound (D R E B : Op H) (hD : IsSkew D) (hB : B.IsSymmetric) (u : H)
    (A C L n : ℝ) (hA : 0 ≤ A) (hC : 0 ≤ C) (hL : 0 ≤ L) (hn : 0 ≤ n)
    (hm : ∀ v, ‖R v‖ ≤ A * ‖v‖) (hlip : ∀ v, ‖comm R B v‖ ≤ L * ‖v‖)
    (hd : ‖D u‖ ≤ n) (he : ‖E u‖ ≤ n)
    (hcd : ‖comm D B u‖ ≤ C * n) (hce : ‖comm E B u‖ ≤ C * n) :
    ‖⟪u, comm (-(D * R * E)) B u⟫_ℂ‖ ≤ (2 * A * C + L) * n^2 := by
  rw [weak_divergence_commutator D R E B hD hB u]
  have p1 := (norm_inner_le_norm (𝕜 := ℂ) (D u) (R (comm E B u))).trans
    (mul_le_mul hd ((hm _).trans (mul_le_mul_of_nonneg_left hce hA)) (norm_nonneg _) hn)
  have p2 := (norm_inner_le_norm (𝕜 := ℂ) (D u) (comm R B (E u))).trans
    (mul_le_mul hd ((hlip _).trans (mul_le_mul_of_nonneg_left he hL)) (norm_nonneg _) hn)
  have p3 := (norm_inner_le_norm (𝕜 := ℂ) (comm D B u) (R (E u))).trans
    (mul_le_mul hcd ((hm _).trans (mul_le_mul_of_nonneg_left he hA)) (norm_nonneg _) (mul_nonneg hC hn))
  calc
    _ ≤ (‖⟪D u, R (comm E B u)⟫_ℂ‖ + ‖⟪D u, comm R B (E u)⟫_ℂ‖) +
        ‖⟪comm D B u, R (E u)⟫_ℂ‖ :=
      (norm_sub_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ n * (A * (C * n)) + n * (L * n) + (C * n) * (A * n) := add_le_add (add_le_add p1 p2) p3
    _ = _ := by ring

end Burnett.Analysis.SymmetricEnergy
