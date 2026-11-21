import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.SymmetricEnergy

open scoped InnerProductSpace BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
abbrev Op (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] := H →ₗ[ℂ] H

def comm (A B : Op H) := A * B - B * A

/-- All three terms of the first-order commutator with one divergence-form summand. -/
theorem divergence_commutator_term (D R E B : Op H) :
    comm (-(D * R * E)) B =
      -(D * R * comm E B) - D * comm R B * E - comm D B * R * E := by
  unfold comm
  noncomm_ring

variable {ι : Type*} [Fintype ι]

def divergence (D : ι → Op H) (R : ι → ι → Op H) : Op H :=
  -∑ a, ∑ b, D a * R a b * D b

/-- Integration by parts twice and interchange of the two ordered indices
make the divergence operator symmetric also for matrix coefficients. -/
theorem divergence_isSymmetric (D : ι → Op H) (R : ι → ι → Op H)
    (hD : ∀ a x y, ⟪D a x, y⟫_ℂ = -⟪x, D a y⟫_ℂ)
    (hR : ∀ a b x y, ⟪R a b x, y⟫_ℂ = ⟪x, R b a y⟫_ℂ) : (divergence D R).IsSymmetric := by
  intro x y
  simp only [divergence, LinearMap.neg_apply, LinearMap.sum_apply, Module.End.mul_apply,
    inner_neg_left, inner_neg_right, sum_inner, inner_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [hD, hR, hD, neg_neg]

/-- The manuscript uses a first-slot-linear pairing. In Lean its imaginary
part is the imaginary part of the pairing with the two arguments reversed. -/
theorem imaginary_energy_eq_commutator (L B : Op H) (hL : L.IsSymmetric) (hB : B.IsSymmetric) (u : H) :
    2 * (⟪B u, L u⟫_ℂ).im = (⟪u, Complex.I • comm L B u⟫_ℂ).re := by
  have hswap : (⟪L u, B u⟫_ℂ).im = -(⟪B u, L u⟫_ℂ).im := inner_im_symm (𝕜 := ℂ) _ _
  simp only [comm, LinearMap.sub_apply, Module.End.mul_apply, inner_smul_right,
    inner_sub_right, ← hL u (B u), ← hB u (L u), Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.sub_im, zero_mul, one_mul, zero_sub, hswap]
  ring

end Burnett.Analysis.SymmetricEnergy
