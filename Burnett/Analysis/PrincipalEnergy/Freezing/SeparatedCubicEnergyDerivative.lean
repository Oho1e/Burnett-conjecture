import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedCubicEnergyBound
import Burnett.Analysis.PrincipalEnergy.Freezing.PrincipalCubicScalarVariation
import Burnett.Analysis.CubicEnergy.CompleteEnergy.UniformWeightedEuclidean

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FieldAndCoefficientReview
open scoped ComplexConjugate ContDiff ENNReal

/-- Enumerate every entry of the actual cubic coefficient array. -/
def separatedCubicCoefficientField {J : Type}
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (p : Index × Index × J × J × J) : SchwartzMap E ℂ :=
  C p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- The paper's directional cubic action derivative and its polarized
third variation use the true Euclidean coefficient and field arrays. -/
theorem separated_principal_action_derivatives_bound {J : Type} [Fintype J] :
    ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {x | x ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) →
      (∀ ξ, b (-ξ) = -b ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f : SchwartzMap E ℂ) (C : Index → Index → J → J → J → SchwartzMap E ℂ)
        (z : J → SchwartzMap E ℂ),
      (∀ x, conj (f x) = f x) → (∀ a d i j k, C a d i j k = C d a i k j) →
      (∀ j x, conj (z j x) = z j x) →
      let X := euclideanFieldGradientNorm z
      let Y := eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume
      let C₀ := eLpNorm (fieldValueArray (separatedCubicCoefficientField C)) ⊤ volume
      let C₁ := eLpNorm (euclideanFieldGradient (separatedCubicCoefficientField C)) ⊤ volume
      let F₀ := eLpNorm (f : E → ℂ) ⊤ volume
      let F₁ := eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume
      let F₂ := eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume
      let B := K * ENNReal.ofReal D * separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y
      let w (i : J) := separatedSkewAction f b (z i)
      B < ⊤ ∧ ‖deriv (fun t : ℝ => principalCubicAction C (fun i y => z i y + t • w i y)) 0‖ₑ ≤ B ∧
      ‖deriv (fun s : ℝ => deriv (fun r : ℝ => deriv (fun t : ℝ =>
        principalCubicAction C (fun i y => r • z i y + t • w i y)) 0) s) 0‖ₑ ≤ 2 * B := by
  obtain ⟨K, hK, bound⟩ := separated_principal_variation_bound (J := J)
  refine ⟨K, hK, ?_⟩
  intro b hb hom hodd D hD jet f C z hf symm hz X Y C₀ C₁ F₀ F₁ F₂ B w
  have hc₀ (a d : Index) (i j k : J) :
      eLpNorm (C a d i j k : E → ℂ) ⊤ volume ≤ C₀ :=
    eLpNorm_mono (f := (C a d i j k : E → ℂ)) (g := fieldValueArray (separatedCubicCoefficientField C))
      (fun x => PiLp.norm_apply_le (fieldValueArray (separatedCubicCoefficientField C) x) (a, d, i, j, k))
  have hc₁ (a d : Index) (i j k : J) (l : Index) :
      eLpNorm (energyPartial l (C a d i j k) : E → ℂ) ⊤ volume ≤ C₁ :=
    eLpNorm_mono (f := (energyPartial l (C a d i j k) : E → ℂ))
      (g := euclideanFieldGradient (separatedCubicCoefficientField C))
      (fun x => PiLp.norm_apply_le (euclideanFieldGradient (separatedCubicCoefficientField C) x)
        (l, (a, d, i, j, k)))
  have hEnergy := bound b hb hom hodd D hD jet f C z C₀ C₁ hc₀ hc₁ hf symm hz
  obtain ⟨hFirst, hThird⟩ := separated_principal_variation_action_derivatives C z f b hb hom
  have hX : X < ⊤ := euclideanFieldGradientNorm_lt_top z
  have hY : Y < ⊤ := (fieldValueArray_memLp z _).eLpNorm_lt_top
  have hC₀ : C₀ < ⊤ := (fieldValueArray_memLp (separatedCubicCoefficientField C) _).eLpNorm_lt_top
  have hC₁ : C₁ < ⊤ := (euclideanFieldGradient_memLp (separatedCubicCoefficientField C) _).eLpNorm_lt_top
  have hF₀ : F₀ < ⊤ := (f.memLp ⊤ volume).eLpNorm_lt_top
  have hF₁ : F₁ < ⊤ := ((SchwartzMap.fderivCLM ℝ f).memLp ⊤ volume).eLpNorm_lt_top
  have hF₂ : F₂ < ⊤ := by
    change eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume < ⊤
    rw [eLpNorm_exponent_top]
    obtain ⟨c, _, hc⟩ := f.decay 0 2
    exact eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall fun x => by
      simpa only [pow_zero, one_mul] using hc x)
  have hRhs : separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y < ⊤ := by
    unfold separatedCubicBoundRhs
    have h₀ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₀ hF₀) (ENNReal.pow_lt_top (n := 3) hX)
    have h₁ := ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top hC₀ hF₁, ENNReal.mul_lt_top hC₁ hF₀⟩
    have h₂ := ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₀ hF₂) (ENNReal.pow_lt_top (n := 2) hY)
    exact ENNReal.add_lt_top.mpr
      ⟨ENNReal.add_lt_top.mpr ⟨h₀, ENNReal.mul_lt_top (ENNReal.mul_lt_top h₁ hY) (ENNReal.pow_lt_top hX)⟩,
        ENNReal.mul_lt_top h₂ hX⟩
  refine ⟨ENNReal.mul_lt_top (ENNReal.mul_lt_top hK ENNReal.ofReal_lt_top) hRhs, ?_, ?_⟩
  · rw [hFirst.deriv]
    exact hEnergy
  · rw [hThird]
    calc
      _ = 2 * ‖∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z w x‖ₑ := by
        rw [Complex.real_smul]
        simp [enorm_eq_nnnorm, w]
      _ ≤ _ := mul_le_mul_left' hEnergy _

end Burnett.A02.FrequencySplit
