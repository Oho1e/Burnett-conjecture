import Burnett.Analysis.PrincipalEnergy.Freezing.GeneralCubicFreezing
import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCubicPolynomial
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false
set_option maxHeartbeats 11000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators ContDiff

open private principal_cubic_density_polynomial from Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCubicPolynomial
open private weighted_cubic_integrable lowerValueTest lowerDerivativeTest from Burnett.Analysis.PrincipalEnergy.Freezing.GeneralLowerCubicAction

private theorem integral_cubic_diagonal_difference (A B C V : E → ℂ)
    (hA : Integrable A) (hB : Integrable B) (hC : Integrable C)
    (h : ∀ x, A x - B x - 2 * C x = 2 * V x) :
    (∫ x, A x) - (∫ x, B x) - 2 * (∫ x, C x) = 2 * (∫ x, V x) := by
  have left : (∫ x, A x - B x - 2 * C x) = (∫ x, A x) - (∫ x, B x) - 2 * (∫ x, C x) := by
    calc
      _ = (∫ x, A x - B x) - ∫ x, 2 * C x := integral_sub (hA.sub hB) (hC.const_mul 2)
      _ = _ := by rw [integral_sub hA hB, integral_const_mul]
  rw [← left, ← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall h)

/-- The diagonal principal polynomial with the original coefficient
placement. Bounded coefficients include the constant frozen array. -/
def realPrincipalCubicPolynomial {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ) (z : J → SchwartzMap E ℂ) : ℝ :=
  (∫ x, principalCubicMixedDensity (fun a d i j k x => (C a d i j k x : ℂ))
    (fun i => z i) (fun i => z i) (fun i => z i) x).re

private theorem integrable_real_principal_density {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hMeas : ∀ a d i j k, Measurable (C a d i j k))
    (M : ℝ) (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (u v w : J → SchwartzMap E ℂ) :
    Integrable (principalCubicMixedDensity (fun a d i j k x => (C a d i j k x : ℂ))
      (fun i => u i) (fun i => v i) (fun i => w i)) := by
  unfold principalCubicMixedDensity
  apply integrable_finset_sum Finset.univ
  intro a _
  apply integrable_finset_sum Finset.univ
  intro d _
  apply integrable_finset_sum Finset.univ
  intro i _
  apply integrable_finset_sum Finset.univ
  intro j _
  apply integrable_finset_sum Finset.univ
  intro k _
  let f := energyProduct (energyProduct (u i) (energyPartial a (v j))) (energyPartial d (w k))
  change Integrable (fun x => (C a d i j k x : ℂ) * f x)
  refine (f.integrable.norm.const_mul M).mono'
    ((Complex.continuous_ofReal.measurable.comp (hMeas a d i j k)).mul f.continuous.measurable).aestronglyMeasurable ?_
  filter_upwards with x
  rw [norm_mul, Complex.norm_real]
  exact mul_le_mul_of_nonneg_right (hValue a d i j k x) (norm_nonneg _)

/-- The real diagonal difference recovers the exact three placements in
the principal cubic action, for variable and frozen coefficients alike. -/
theorem realPrincipalCubicPolynomial_polarize {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hMeas : ∀ a d i j k, Measurable (C a d i j k))
    (M : ℝ) (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (z w : J → SchwartzMap E ℂ) :
    realPrincipalCubicPolynomial C (z + w) - realPrincipalCubicPolynomial C (z - w) -
      2 * realPrincipalCubicPolynomial C w = 2 * realPrincipalVariation C z (fun i => w i) := by
  let coeff (a d : Index) (i j k : J) (x : E) := (C a d i j k x : ℂ)
  let P (v : J → SchwartzMap E ℂ) := principalCubicMixedDensity coeff (fun i => v i) (fun i => v i) (fun i => v i)
  let V := principalVariationDensity coeff z (fun i => w i)
  let L (u v : J → SchwartzMap E ℂ) := principalCubicLinearDensity coeff (fun i => u i) (fun i => v i)
  have hInt := integrable_real_principal_density C hMeas M hValue
  have hVI : Integrable V := by
    rw [show V = L z w from (principal_cubic_linear_density_eq_variation coeff z (fun i => w i)).symm]
    exact ((hInt w z z).add (hInt z w z)).add (hInt z z w)
  have point (x : E) : P (z + w) x - P (z - w) x - 2 * P w x = 2 * V x := by
    have hPlus : P (z + w) x = P z x + L z w x + L w z x + P w x := by
      simpa only [P, L, Pi.add_apply, SchwartzMap.add_apply, one_pow, one_mul, one_smul] using
        principal_cubic_density_polynomial coeff (fun i => z i) (fun i => w i)
          (fun i => (z i).differentiable) (fun i => (w i).differentiable) 1 1 x
    have hMinus : P (z - w) x = P z x - L z w x + L w z x - P w x := by
      have h := principal_cubic_density_polynomial coeff (fun i => z i) (fun i => w i)
        (fun i => (z i).differentiable) (fun i => (w i).differentiable) 1 (-1) x
      rw [show (-1 : ℝ) ^ 3 = -1 by norm_num] at h
      simpa [P, L, SchwartzMap.sub_apply, ← sub_eq_add_neg] using h
    rw [hPlus, hMinus, show V = L z w from (principal_cubic_linear_density_eq_variation coeff z (fun i => w i)).symm]
    ring
  have h := integral_cubic_diagonal_difference (P (z + w)) (P (z - w)) (P w) V
    (hInt _ _ _) (hInt _ _ _) (hInt _ _ _) point
  have hRe : (∫ x, (V x).re) = (∫ x, V x).re := integral_re hVI
  change (∫ x, P (z + w) x).re - (∫ x, P (z - w) x).re -
    2 * (∫ x, P w x).re = 2 * ∫ x, (V x).re
  rw [hRe]
  simpa [Complex.sub_re, Complex.mul_re] using congrArg Complex.re h

private theorem weighted_cubic_diagonal_difference (c u v w U V W : SchwartzMap E ℂ) :
    weightedCubicIntegral c (u + U) (v + V) (w + W) -
      weightedCubicIntegral c (u - U) (v - V) (w - W) - 2 * weightedCubicIntegral c U V W =
      2 * lowerValueTest c u v w U V W := by
  let A (x : E) := c x * (u + U) x * (v + V) x * (w + W) x
  let B (x : E) := c x * (u - U) x * (v - V) x * (w - W) x
  let C (x : E) := c x * U x * V x * W x
  let F (x : E) := c x * U x * v x * w x + c x * u x * V x * w x + c x * u x * v x * W x
  have point (x : E) : A x - B x - 2 * C x = 2 * F x := by
    simp only [A, B, C, F, SchwartzMap.add_apply, SchwartzMap.sub_apply]
    ring
  have h := integral_cubic_diagonal_difference A B C F
    (weighted_cubic_integrable c _ _ _) (weighted_cubic_integrable c _ _ _) (weighted_cubic_integrable c U V W) point
  have fSum : (∫ x, F x) = lowerValueTest c u v w U V W := by
    unfold F lowerValueTest weightedCubicIntegral
    have h₁ := weighted_cubic_integrable c U v w
    have h₂ := weighted_cubic_integrable c u V w
    have h₃ := weighted_cubic_integrable c u v W
    calc
      _ = (∫ x, c x * U x * v x * w x + c x * u x * V x * w x) + ∫ x, c x * u x * v x * W x :=
        integral_add (h₁.add h₂) h₃
      _ = _ := congrArg (fun z => z + ∫ x, c x * u x * v x * W x) (integral_add h₁ h₂)
  rwa [← show weightedCubicIntegral c (u + U) (v + V) (w + W) = ∫ x, A x from rfl,
    ← show weightedCubicIntegral c (u - U) (v - V) (w - W) = ∫ x, B x from rfl,
    ← show weightedCubicIntegral c U V W = ∫ x, C x from rfl, fSum] at h

/-- Every lower-order term has the same symmetric diagonal normalization.
The identity uses the entire variation, including the differentiated slot. -/
theorem lowerCubicPolynomial_polarize {J : Type} [Fintype J]
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (z w : J → SchwartzMap E ℂ) :
    lowerCubicPolynomial C₀ C₁ (z + w) - lowerCubicPolynomial C₀ C₁ (z - w) -
      2 * lowerCubicPolynomial C₀ C₁ w = 2 * realLowerCubicVariation C₀ C₁ z w := by
  let P₀ (v : J → SchwartzMap E ℂ) (i : J × J × J) :=
    weightedCubicIntegral (C₀ i) (v i.1) (v i.2.1) (v i.2.2)
  let P₁ (v : J → SchwartzMap E ℂ) (i : Index × J × J × J) :=
    weightedCubicIntegral (C₁ i) (v i.2.1) (v i.2.2.1) (energyPartial i.1 (v i.2.2.2))
  let T₀ (i : J × J × J) :=
    lowerValueTest (C₀ i) (z i.1) (z i.2.1) (z i.2.2) (w i.1) (w i.2.1) (w i.2.2)
  let T₁ (i : Index × J × J × J) := lowerDerivativeTest i.1 (C₁ i)
    (z i.2.1) (z i.2.2.1) (z i.2.2.2) (w i.2.1) (w i.2.2.1) (w i.2.2.2)
  have h₀ : (∑ i, P₀ (z + w) i) - (∑ i, P₀ (z - w) i) - 2 * (∑ i, P₀ w i) = 2 * (∑ i, T₀ i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    exact weighted_cubic_diagonal_difference _ _ _ _ _ _ _
  have h₁ : (∑ i, P₁ (z + w) i) - (∑ i, P₁ (z - w) i) - 2 * (∑ i, P₁ w i) = 2 * (∑ i, T₁ i) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [P₁, T₁, lowerDerivativeTest, energyPartial, Pi.add_apply, Pi.sub_apply, map_add, map_sub]
      using weighted_cubic_diagonal_difference (C₁ i) (z i.2.1) (z i.2.2.1)
        (energyPartial i.1 (z i.2.2.2)) (w i.2.1) (w i.2.2.1) (energyPartial i.1 (w i.2.2.2))
  have hAll : ((∑ i, P₀ (z + w) i) + ∑ i, P₁ (z + w) i) -
      ((∑ i, P₀ (z - w) i) + ∑ i, P₁ (z - w) i) - 2 * ((∑ i, P₀ w i) + ∑ i, P₁ w i) =
        2 * ((∑ i, T₀ i) + ∑ i, T₁ i) := by
    linear_combination h₀ + h₁
  simpa [lowerCubicPolynomial, realLowerCubicVariation, P₀, P₁, T₀, T₁, Complex.sub_re, Complex.mul_re]
    using congrArg Complex.re hAll

end Burnett.A03
