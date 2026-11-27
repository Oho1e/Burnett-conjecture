import Burnett.Analysis.PrincipalEnergy.Freezing.GeneralCubicPolarization
import Mathlib.Tactic.Linarith

set_option autoImplicit false
set_option maxHeartbeats 10500000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ComplexConjugate ContDiff

/-- A real trilinear action invariant under the two adjacent transpositions. -/
structure SymmetricTrilinearAction (V : Type*) [AddCommGroup V] [Module ℝ V] where
  action : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  swapFirst : ∀ u v w, action u v w = action v u w
  swapLast : ∀ u v w, action u v w = action u w v

namespace SymmetricTrilinearAction

theorem diagonal_difference {V : Type*} [AddCommGroup V] [Module ℝ V]
    (T : SymmetricTrilinearAction V) (z w : V) :
    T.action (z + w) (z + w) (z + w) - T.action (z - w) (z - w) (z - w) -
      2 * T.action w w w = 6 * T.action z z w := by
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply]
  simp_rw [T.swapFirst w z z, T.swapLast z w z]
  ring

end SymmetricTrilinearAction

/-- The complete three test placements are forced by symmetry and the
original diagonal polynomial of the action. -/
theorem symmetricAction_test_of_diagonal {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hMeas : ∀ a d i j k, Measurable (C a d i j k))
    (M : ℝ) (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (T : SymmetricTrilinearAction (RealEnergyField J))
    (hDiag : ∀ v, T.action v v v = realPrincipalCubicPolynomial C v.val + lowerCubicPolynomial C₀ C₁ v.val)
    (z w : RealEnergyField J) : T.action z z w = realCompleteCubicTest C C₀ C₁ z.val w.val := by
  have hT := T.diagonal_difference z w
  simp only [hDiag] at hT
  have hC := realPrincipalCubicPolynomial_polarize C hMeas M hValue z.val w.val
  have hL := lowerCubicPolynomial_polarize C₀ C₁ z.val w.val
  change (realPrincipalCubicPolynomial C (z.val + w.val) + lowerCubicPolynomial C₀ C₁ (z.val + w.val)) -
    (realPrincipalCubicPolynomial C (z.val - w.val) + lowerCubicPolynomial C₀ C₁ (z.val - w.val)) -
      2 * (realPrincipalCubicPolynomial C w.val + lowerCubicPolynomial C₀ C₁ w.val) = _ at hT
  unfold realCompleteCubicTest
  linarith only [hT, hC, hL]

/-- The frozen real action is the symmetric polarization of the actual
center-value principal polynomial. -/
theorem symmetricFrozenAction_test_of_diagonal {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ) (c : E)
    (M : ℝ) (hValue : ∀ a d i j k, ‖C a d i j k c‖ ≤ M)
    (T : SymmetricTrilinearAction (RealEnergyField J))
    (hDiag : ∀ v, T.action v v v = realPrincipalCubicPolynomial (fun a d i j k _ => C a d i j k c) v.val)
    (z w : RealEnergyField J) : T.action z z w = realFrozenCubicTest C c z.val w.val := by
  let Cc (a d : Index) (i j k : J) (_ : E) := C a d i j k c
  have hT := T.diagonal_difference z w
  simp only [hDiag] at hT
  have hC := realPrincipalCubicPolynomial_polarize Cc (fun _ _ _ _ _ => measurable_const)
    M (fun a d i j k _ => hValue a d i j k) z.val w.val
  change realPrincipalCubicPolynomial Cc (z.val + w.val) - realPrincipalCubicPolynomial Cc (z.val - w.val) -
    2 * realPrincipalCubicPolynomial Cc w.val = _ at hT
  unfold realFrozenCubicTest
  linarith only [hT, hC]

/-- The same scalar skew test acts on each field component. -/
def realSkewCubicTest {J : Type} (B : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hReal : ∀ u : SchwartzMap E ℂ, (∀ x, conj (u x) = u x) →
      ∀ x, conj ((-Complex.I) * B u x) = (-Complex.I) * B u x)
    (z : RealEnergyField J) : RealEnergyField J :=
  ⟨fun i => (-Complex.I) • B (z.val i), fun i x => by
    simpa only [SchwartzMap.smul_apply, smul_eq_mul] using hReal (z.val i) (z.property i) x⟩

/-- Manuscript lines 736–764 in the compact coordinate Weyl representation.
The two symmetric actions are supplied by their original diagonal polynomials.
The only operator input beyond the representation is the stated reality of
the skew test. Both constants are selected before the patch center and field. -/
theorem exists_symmetric_action_freezing {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hSmooth : ∀ a d i j k, ContDiff ℝ ∞ (C a d i j k))
    (hCompact : ∀ a d i j k, HasCompactSupport (C a d i j k))
    (hSymm : ∀ a d i j k, C a d i j k = C d a i k j)
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (T : SymmetricTrilinearAction (RealEnergyField J)) (T₀ : E → SymmetricTrilinearAction (RealEnergyField J))
    (hDiag : ∀ v, T.action v v v = realPrincipalCubicPolynomial C v.val + lowerCubicPolynomial C₀ C₁ v.val)
    (hFrozenDiag : ∀ c v, (T₀ c).action v v v = realPrincipalCubicPolynomial (fun a d i j k _ => C a d i j k c) v.val)
    (R L M ℓ₀ : ℝ) (hR : 0 < R) (hL : 0 ≤ L) (hℓ₀ : ℓ₀ ≤ 1)
    (hGrad : ∀ a d i j k x, ‖fderiv ℝ (C a d i j k) x‖ ≤ L)
    (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (test : CompactScalarWeylTest)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ) (B₀ : E → SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u, (B u : E → ℂ) = test.action u)
    (hB₀ : ∀ c u, (B₀ c u : E → ℂ) = test.frozenAction c u)
    (hReal : ∀ u : SchwartzMap E ℂ, (∀ x, conj (u x) = u x) →
      ∀ x, conj ((-Complex.I) * B u x) = (-Complex.I) * B u x)
    (hFrozenReal : ∀ c (u : SchwartzMap E ℂ), (∀ x, conj (u x) = u x) →
      ∀ x, conj ((-Complex.I) * B₀ c u x) = (-Complex.I) * B₀ c u x) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ ℓ₀ → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (c : E) (z : RealEnergyField J), tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        |T.action z z (realSkewCubicTest B hReal z) -
          (T₀ c).action z z (realSkewCubicTest (B₀ c) (hFrozenReal c) z)| ≤
          A * ℓ * euclideanFieldGradientL3 z.val ^ 3 +
          D * euclideanFieldValueL3 z.val * euclideanFieldGradientL3 z.val ^ 2 := by
  have hMeas (a d : Index) (i j k : J) : Measurable (C a d i j k) := (hSmooth a d i j k).continuous.measurable
  obtain ⟨A, hA, energy⟩ := exists_general_complete_cubic_freezing_bound C hSmooth hCompact hSymm
    C₀ C₁ R L M hR hL hGrad hValue test B B₀ hB hB₀
  refine ⟨A, hA, ?_⟩
  intro ℓ hℓ hℓle
  obtain ⟨D, hD, patch⟩ := energy ℓ hℓ (hℓle.trans hℓ₀)
  refine ⟨D, hD, ?_⟩
  intro c z hz
  rw [symmetricAction_test_of_diagonal C hMeas M hValue C₀ C₁ T hDiag z,
    symmetricFrozenAction_test_of_diagonal C c M (fun a d i j k => hValue a d i j k c) (T₀ c) (hFrozenDiag c) z]
  exact patch c z hz

end Burnett.A03
