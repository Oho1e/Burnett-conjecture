import Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectionEnergyPairing
import Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousProjectionWeakDerivative

/-! Actual whole-space matrix multipliers and their norm pairings. -/

set_option autoImplicit false
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.C02

open Filter Function MeasureTheory Set Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference (CoordinateSpace)
open Burnett.RicciSymbol (Index)
open Burnett.A07 (coordinateDerivative)
open Burnett.Microlocal.Overlap (classicalLeftPairing)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Microlocal.SeparablePositive
  (conjugateSymbol conjugateSymbol_apply productSymbol productSymbol_apply
    fourierMultiplier_product inner_fourierMultiplier_left)
open scoped BigOperators ComplexConjugate ContDiff InnerProduct Matrix Topology

open private fourierMultiplier_classicalLeftPairing
  from Burnett.Analysis.GaugeProjection.StrongCompactness.ProjectionEnergyPairing
open private inner_derivative_fourierMultiplier
  from Burnett.Analysis.GaugeProjection.StrongCompactness.HomogeneousProjectionWeakDerivative

local notation "E" => CoordinateSpace

/-- The actual matrix entries are Fourier multipliers smooth at zero.
For a base-independent classical order-zero symbol, the usual principal
and order-minus-one estimates give exactly the fields used below. -/
structure ClassicalMatrixMultiplier (J : Type*) where
  full : J → OrderedPair → BoundedSymbol E
  principal : E → Matrix J OrderedPair ℂ
  full_smooth : ∀ k i, ContDiff ℝ ∞ (full k i : E → ℂ)
  principal_smooth : ∀ k i, ContDiffOn ℝ ∞ (fun ξ => principal ξ k i) ({0}ᶜ : Set E)
  principal_degree : ∀ k i (t : ℝ), 0 < t → ∀ ξ : E, ξ ≠ 0 →
    principal (t • ξ) k i = principal ξ k i
  order_minus_one : ∀ k i, ∃ R C : ℝ, 0 ≤ C ∧ ∀ ξ : E, R ≤ ‖ξ‖ →
    (1 + ‖ξ‖) * ‖full k i ξ - principal ξ k i‖ ≤ C

variable {J : Type*}

def ClassicalMatrixMultiplier.output (T : ClassicalMatrixMultiplier J)
    (u : OrderedPair → ComplexL2 E) (k : J) : ComplexL2 E :=
  ∑ i : OrderedPair, fourierMultiplier (T.full k i) (u i)

def ClassicalMatrixMultiplier.energySymbol (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) : BoundedSymbol E :=
  productSymbol (conjugateSymbol (T.full k i)) (T.full k j)

def ClassicalMatrixMultiplier.energyPrincipal (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) (ξ : E) : ℂ :=
  conj (T.principal ξ k i) * T.principal ξ k j

theorem ClassicalMatrixMultiplier.energySymbol_smooth (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) : ContDiff ℝ ∞ (T.energySymbol k i j : E → ℂ) :=
  (Complex.conjCLE.contDiff.comp (T.full_smooth k i)).mul (T.full_smooth k j)

theorem ClassicalMatrixMultiplier.energyPrincipal_smooth (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) :
    ContDiffOn ℝ ∞ (T.energyPrincipal k i j) ({0}ᶜ : Set E) :=
  (Complex.conjCLE.contDiff.comp_contDiffOn (T.principal_smooth k i)).mul (T.principal_smooth k j)

theorem ClassicalMatrixMultiplier.energyPrincipal_degree (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) (t : ℝ) (ht : 0 < t) (ξ : E) (hξ : ξ ≠ 0) :
    T.energyPrincipal k i j (t • ξ) = T.energyPrincipal k i j ξ := by
  simp only [energyPrincipal, T.principal_degree k _ t ht ξ hξ]

theorem ClassicalMatrixMultiplier.energySymbol_order_minus_one (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) : ∃ R C : ℝ, 0 ≤ C ∧ ∀ ξ : E, R ≤ ‖ξ‖ →
      (1 + ‖ξ‖) * ‖T.energySymbol k i j ξ - T.energyPrincipal k i j ξ‖ ≤ C := by
  obtain ⟨Ri, Ci, hCi, hi⟩ := T.order_minus_one k i
  obtain ⟨Rj, Cj, hCj, hj⟩ := T.order_minus_one k j
  let Mi := (T.full k i).bound
  let Mj := (T.full k j).bound
  have hMi : 0 ≤ Mi := (T.full k i).bound_nonneg
  have hMj : 0 ≤ Mj := (T.full k j).bound_nonneg
  refine ⟨max Ri Rj, Ci * Mj + (Mi + Ci) * Cj, by positivity, ?_⟩
  intro ξ hξ
  let fi := T.full k i ξ
  let fj := T.full k j ξ
  let pi := T.principal ξ k i
  let pj := T.principal ξ k j
  let w := 1 + ‖ξ‖
  have hw : 0 ≤ w := by positivity
  have hwi : w * ‖fi - pi‖ ≤ Ci := hi ξ ((le_max_left _ _).trans hξ)
  have hwj : w * ‖fj - pj‖ ≤ Cj := hj ξ ((le_max_right _ _).trans hξ)
  have hpi : ‖pi‖ ≤ Mi + Ci := by
    have hwOne : 1 ≤ w := le_add_of_nonneg_right (norm_nonneg ξ)
    have hdiff : ‖fi - pi‖ ≤ Ci := (le_mul_of_one_le_left (norm_nonneg _) hwOne).trans hwi
    calc
      ‖pi‖ = ‖fi - (fi - pi)‖ := by rw [sub_sub_cancel]
      _ ≤ ‖fi‖ + ‖fi - pi‖ := norm_sub_le _ _
      _ ≤ Mi + Ci := add_le_add ((T.full k i).norm_le ξ) hdiff
  have hSplit : conj fi * fj - conj pi * pj = conj (fi - pi) * fj + conj pi * (fj - pj) := by
    rw [map_sub]
    ring
  change w * ‖conj fi * fj - conj pi * pj‖ ≤ _
  rw [hSplit]
  calc
    w * ‖conj (fi - pi) * fj + conj pi * (fj - pj)‖ ≤
        w * (‖fi - pi‖ * ‖fj‖ + ‖pi‖ * ‖fj - pj‖) := by
          apply mul_le_mul_of_nonneg_left _ hw
          simpa only [norm_mul, Complex.norm_conj] using
            norm_add_le (conj (fi - pi) * fj) (conj pi * (fj - pj))
    _ = (w * ‖fi - pi‖) * ‖fj‖ + ‖pi‖ * (w * ‖fj - pj‖) := by ring
    _ ≤ Ci * Mj + (Mi + Ci) * Cj := by
      exact add_le_add
        (mul_le_mul hwi ((T.full k j).norm_le ξ) (norm_nonneg _) hCi)
        (mul_le_mul hpi hwj (mul_nonneg hw (norm_nonneg _)) (add_nonneg hMi hCi))

theorem ClassicalMatrixMultiplier.energySymbol_pairing (T : ClassicalMatrixMultiplier J)
    (k : J) (i j : OrderedPair) (f v : SchwartzMap E ℂ) :
    inner ℂ (f.toLp 2 volume) (fourierMultiplier (T.energySymbol k i j) (v.toLp 2 volume)) =
      classicalLeftPairing (fun _ ξ => T.energySymbol k i j ξ) f v :=
  fourierMultiplier_classicalLeftPairing (T.energySymbol k i j) v f

/-- The squared norm includes all of coordinate space. The adjoint identity
moves both factors to original inputs, without an output cutoff. -/
theorem ClassicalMatrixMultiplier.output_norm_sq (T : ClassicalMatrixMultiplier J)
    (u : OrderedPair → ComplexL2 E) (k : J) :
    ‖T.output u k‖^2 =
      (∑ i : OrderedPair, ∑ j : OrderedPair,
        inner ℂ (u i) (fourierMultiplier (T.energySymbol k i j) (u j))).re := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ), output, sum_inner]
  apply congrArg Complex.re
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [inner_fourierMultiplier_left, energySymbol, fourierMultiplier_product]

theorem ClassicalMatrixMultiplier.principal_covariance_diag (T : ClassicalMatrixMultiplier J)
    (k : J) (ξ : E) (N : Matrix OrderedPair OrderedPair ℂ) :
    (∑ i : OrderedPair, ∑ j : OrderedPair, conj (T.energyPrincipal k i j ξ) * N i j) =
      (T.principal ξ * N * (T.principal ξ)ᴴ) k k := by
  rw [Matrix.mul_assoc]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, energyPrincipal, Complex.star_def, map_mul,
    starRingEnd_self_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- This is the weak Euclidean derivative of the actual whole-space output. -/
theorem ClassicalMatrixMultiplier.output_weak_coordinateDerivative (T : ClassicalMatrixMultiplier J)
    (u : OrderedPair → SchwartzMap E ℂ) (f : SchwartzMap E ℂ) (d : Index) (k : J) :
    inner ℂ ((coordinateDerivative d f).toLp 2 volume) (T.output (fun i => (u i).toLp 2 volume) k) =
      -inner ℂ (f.toLp 2 volume) (T.output (fun i => (coordinateDerivative d (u i)).toLp 2 volume) k) := by
  simp only [output, inner_sum, inner_derivative_fourierMultiplier, Finset.sum_neg_distrib]

theorem ClassicalMatrixMultiplier.output_sub_tendsto_zero (T : ClassicalMatrixMultiplier J)
    (u v : ℕ → OrderedPair → ComplexL2 E)
    (h : ∀ i, Tendsto (fun n => u n i - v n i) atTop (𝓝 0)) (k : J) :
    Tendsto (fun n => T.output (u n) k - T.output (v n) k) atTop (𝓝 0) := by
  have hEntry (i : OrderedPair) :
      Tendsto (fun n => fourierMultiplier (T.full k i) (u n i - v n i)) atTop (𝓝 0) := by
    simpa only [map_zero, Function.comp_def] using
      (((fourierMultiplier (T.full k i)).continuous.tendsto 0).comp (h i))
  simpa only [output, ← Finset.sum_sub_distrib, ← map_sub, Finset.sum_const_zero] using
    tendsto_finset_sum (Finset.univ : Finset OrderedPair) (fun i _ => hEntry i)

end Burnett.C02
