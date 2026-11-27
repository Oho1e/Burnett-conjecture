import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedModeEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalPoincare

set_option autoImplicit false
set_option maxHeartbeats 1700000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ComplexConjugate BigOperators ENNReal

/-- The sum of absolute values of actual separated mode energies has the
patch bound with one constant before the scale, center and truncation. -/
theorem exists_finite_separated_patch_energy_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (symm : ∀ a d i j k, C a d i j k = C d a i k j)
    (R : ℝ) (hR : 0 < R) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ A : ℝ, 0 ≤ A →
      ∀ (I : Type) (c : E) (ℓ : ℝ), 0 < ℓ → ℓ ≤ 1 →
      ∀ z : J → SchwartzMap E ℂ, (∀ i x, conj (z i x) = z i x) →
      tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
      ∀ (modes : Finset I) (f : I → Fin 2 → SchwartzMap E ℂ) (b : I → Fin 2 → E → ℝ)
        (D : I → Fin 2 → ℝ),
        (∀ k j, ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0}) →
        (∀ k j (t : ℝ), 0 < t → ∀ ξ, b k j (t • ξ) = t * b k j ξ) →
        (∀ k j ξ, b k j (-ξ) = -b k j ξ) → (∀ k j, 0 ≤ D k j) →
        (∀ k j n, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (b k j) ξ‖ ≤ D k j) →
        (∀ k j x, conj (f k j x) = f k j x) →
        (∀ r : ℕ, r ≤ 2 →
          (∑ k ∈ modes, ∑ j : Fin 2, D k j * schwartzProfileJetLInfinity r (f k j)) ≤ A * ℓ * (ℓ⁻¹)^r) →
        (∑ k ∈ modes, ∑ j : Fin 2, ‖separatedModeEnergy C z (f k j) (b k j)‖) ≤
          K * A * ℓ * euclideanFieldGradientL3 z ^ 3 := by
  classical
  obtain ⟨Kmode, hKmode, estimate⟩ := exists_separated_mode_energy_real_bound (J := J)
  let C₀ := (eLpNorm (fieldValueArray (separatedCubicCoefficientField C)) ⊤ volume).toReal
  let C₁ := (eLpNorm (euclideanFieldGradient (separatedCubicCoefficientField C)) ⊤ volume).toReal
  let P := 3 * R
  let K := Kmode * (C₀ + C₀ * P + C₁ * P + C₀ * P ^ 2)
  have hC₀ : 0 ≤ C₀ := ENNReal.toReal_nonneg
  have hC₁ : 0 ≤ C₁ := ENNReal.toReal_nonneg
  have hP : 0 ≤ P := by dsimp only [P]; positivity
  refine ⟨K, by dsimp only [K]; positivity, ?_⟩
  intro A hA I c ℓ hℓ hSmall z hz hSupp modes f b D smooth hom odd hD jet hReal profileSums
  let X := euclideanFieldGradientL3 z
  let Y := euclideanFieldValueL3 z
  let w (r : ℕ) (k : I) (j : Fin 2) := D k j * schwartzProfileJetLInfinity r (f k j)
  let W (r : ℕ) := ∑ k ∈ modes, ∑ j : Fin 2, w r k j
  have hX : 0 ≤ X := ENNReal.toReal_nonneg
  have hY : 0 ≤ Y := ENNReal.toReal_nonneg
  have hW (r : ℕ) : 0 ≤ W r := Finset.sum_nonneg fun k _ =>
    Finset.sum_nonneg fun j _ => mul_nonneg (hD k j) (schwartz_profile_jet_Linfinity_nonnegative r (f k j))
  have hPoincare : Y ≤ P * ℓ * X := euclidean_field_patch_poincare z c R ℓ hR hℓ hSupp
  have invScale : ℓ * ℓ⁻¹ = 1 := mul_inv_cancel₀ hℓ.ne'
  have scale₀ : W 0 ≤ A * ℓ := by
    simpa only [W, w, pow_zero, mul_one] using profileSums 0 (by decide)
  have scale₁ : W 1 ≤ A := calc
    _ ≤ A * ℓ * ℓ⁻¹ := by simpa only [W, w, pow_one] using profileSums 1 (by decide)
    _ = A := by rw [mul_assoc, invScale, mul_one]
  have scale₂ : W 2 ≤ A * ℓ⁻¹ := calc
    _ ≤ A * ℓ * (ℓ⁻¹)^2 := profileSums 2 (by decide)
    _ = A * (ℓ * ℓ⁻¹) * ℓ⁻¹ := by ring
    _ = _ := by rw [invScale, mul_one]
  have oneMode (k : I) (j : Fin 2) :
      ‖separatedModeEnergy C z (f k j) (b k j)‖ ≤ Kmode *
        ((C₀ * X ^ 3) * w 0 k j + (C₀ * Y * X ^ 2) * w 1 k j +
          (C₁ * Y * X ^ 2) * w 0 k j + (C₀ * Y ^ 2 * X) * w 2 k j) := by
    refine (estimate (b k j) (smooth k j) (hom k j) (odd k j) (D k j) (hD k j) (jet k j)
      (f k j) C z (hReal k j) symm hz).trans_eq ?_
    change Kmode * D k j *
      (C₀ * schwartzProfileJetLInfinity 0 (f k j) * X ^ 3 +
        (C₀ * schwartzProfileJetLInfinity 1 (f k j) + C₁ * schwartzProfileJetLInfinity 0 (f k j)) * Y * X ^ 2 +
          C₀ * schwartzProfileJetLInfinity 2 (f k j) * Y ^ 2 * X) = _
    dsimp only [w]
    ring
  have sumMode : (∑ k ∈ modes, ∑ j : Fin 2, ‖separatedModeEnergy C z (f k j) (b k j)‖) ≤ Kmode *
      ((C₀ * X ^ 3) * W 0 + (C₀ * Y * X ^ 2) * W 1 +
        (C₁ * Y * X ^ 2) * W 0 + (C₀ * Y ^ 2 * X) * W 2) := by
    refine (Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun j _ => oneMode k j))).trans_eq ?_
    simp only [W, Finset.sum_add_distrib, ← Finset.mul_sum]
  have term₀ : (C₀ * X ^ 3) * W 0 ≤ (C₀ * A) * ℓ * X ^ 3 :=
    (mul_le_mul_of_nonneg_left scale₀ (by positivity)).trans_eq (by ring)
  have term₁ : (C₀ * Y * X ^ 2) * W 1 ≤ (C₀ * P * A) * ℓ * X ^ 3 := calc
    _ ≤ (C₀ * (P * ℓ * X) * X ^ 2) * A :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPoincare hC₀) (sq_nonneg X))
        scale₁ (hW 1) (by positivity)
    _ = _ := by ring
  have derivativeCoefficient : (C₁ * Y * X ^ 2) * W 0 ≤ (C₁ * P * A) * ℓ * X ^ 3 := calc
    _ ≤ (C₁ * (P * ℓ * X) * X ^ 2) * (A * ℓ) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hPoincare hC₁) (sq_nonneg X))
        scale₀ (hW 0) (by positivity)
    _ = ((C₁ * P * A) * ℓ * X ^ 3) * ℓ := by ring
    _ ≤ _ := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hSmall
        (show 0 ≤ (C₁ * P * A) * ℓ * X ^ 3 by positivity)
  have term₂ : (C₀ * Y ^ 2 * X) * W 2 ≤ (C₀ * P ^ 2 * A) * ℓ * X ^ 3 := calc
    _ ≤ (C₀ * (P * ℓ * X) ^ 2 * X) * (A * ℓ⁻¹) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ hY hPoincare 2) hC₀) hX) scale₂ (hW 2) (by positivity)
    _ = (C₀ * P ^ 2 * A) * ℓ * X ^ 3 * (ℓ * ℓ⁻¹) := by ring
    _ = _ := by rw [invScale, mul_one]
  refine sumMode.trans (mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add (add_le_add term₀ term₁) derivativeCoefficient) term₂) hKmode |>.trans_eq ?_)
  change Kmode * _ = K * A * ℓ * X ^ 3
  dsimp only [K]
  ring

end Burnett.A03
