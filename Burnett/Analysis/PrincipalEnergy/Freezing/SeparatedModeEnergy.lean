import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedCubicEnergyDerivative

set_option autoImplicit false
set_option maxHeartbeats 900000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ComplexConjugate ENNReal

/-- The actual real-parameter cubic action variation for a single separated mode. -/
def separatedModeEnergy {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (f : SchwartzMap E ℂ) (b : E → ℝ) : ℂ :=
  deriv (fun t : ℝ => principalCubicAction C
    (fun i x => z i x + t • separatedSkewAction f b (z i) x)) 0

/-- The spatial profile seminorm used in the real weighted sums. -/
def schwartzProfileJetLInfinity (r : ℕ) (f : SchwartzMap E ℂ) : ℝ :=
  (eLpNorm (iteratedFDeriv ℝ r (f : E → ℂ)) ⊤ volume).toReal

theorem schwartz_profile_jet_Linfinity_nonnegative (r : ℕ) (f : SchwartzMap E ℂ) :
    0 ≤ schwartzProfileJetLInfinity r f :=
  ENNReal.toReal_nonneg

private theorem schwartz_profile_jet_Linfinity_lt_top (r : ℕ) (f : SchwartzMap E ℂ) :
    eLpNorm (iteratedFDeriv ℝ r (f : E → ℂ)) ⊤ volume < ⊤ := by
  rw [eLpNorm_exponent_top]
  obtain ⟨c, _, hc⟩ := f.decay 0 r
  exact eLpNormEssSup_lt_top_of_ae_bound (Filter.Eventually.of_forall fun x => by
    simpa only [pow_zero, one_mul] using hc x)

private theorem schwartz_profile_jet_Linfinity_zero (f : SchwartzMap E ℂ) :
    schwartzProfileJetLInfinity 0 f = (eLpNorm (f : E → ℂ) ⊤ volume).toReal := by
  unfold schwartzProfileJetLInfinity
  congr 1
  exact eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun _ => norm_iteratedFDeriv_zero)

private theorem schwartz_profile_jet_Linfinity_one (f : SchwartzMap E ℂ) :
    schwartzProfileJetLInfinity 1 f = (eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume).toReal := by
  unfold schwartzProfileJetLInfinity
  congr 1
  apply eLpNorm_congr_norm_ae
  apply Filter.Eventually.of_forall
  intro x
  simpa only [norm_iteratedFDeriv_zero, zero_add] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := (f : E → ℂ)) (x := x) (n := 0)).symm

private theorem separated_cubic_bound_toReal
    (C₀ C₁ F₀ F₁ F₂ X Y : ℝ≥0∞) (hC₀ : C₀ < ⊤) (hC₁ : C₁ < ⊤)
    (hF₀ : F₀ < ⊤) (hF₁ : F₁ < ⊤) (hF₂ : F₂ < ⊤) (hX : X < ⊤) (hY : Y < ⊤) :
    (separatedCubicBoundRhs C₀ C₁ F₀ F₁ F₂ X Y).toReal =
      C₀.toReal * F₀.toReal * X.toReal ^ 3 +
        (C₀.toReal * F₁.toReal + C₁.toReal * F₀.toReal) * Y.toReal * X.toReal ^ 2 +
        C₀.toReal * F₂.toReal * Y.toReal ^ 2 * X.toReal := by
  unfold separatedCubicBoundRhs
  have h₁ := ENNReal.mul_lt_top hC₀ hF₁
  have h₂ := ENNReal.mul_lt_top hC₁ hF₀
  have hA := ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₀ hF₀) (ENNReal.pow_lt_top (n := 3) hX)
  have hB := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨h₁, h₂⟩) hY)
    (ENNReal.pow_lt_top (n := 2) hX)
  have hC := ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.mul_lt_top hC₀ hF₂)
    (ENNReal.pow_lt_top (n := 2) hY)) hX
  rw [ENNReal.toReal_add (ENNReal.add_lt_top.mpr ⟨hA,hB⟩).ne hC.ne,
    ENNReal.toReal_add hA.ne hB.ne]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_add h₁.ne h₂.ne]

/-- The actual mode energy in real-valued physical norms, ready for the
same order-by-order weighted spatial sums. -/
theorem exists_separated_mode_energy_real_bound {J : Type} [Fintype J] :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      (∀ ξ, b (-ξ) = -b ξ) → ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (f : SchwartzMap E ℂ) (C : Index → Index → J → J → J → SchwartzMap E ℂ)
        (z : J → SchwartzMap E ℂ),
        (∀ x, conj (f x) = f x) → (∀ a d i j k, C a d i j k = C d a i k j) →
        (∀ i x, conj (z i x) = z i x) →
        let X := euclideanFieldGradientL3 z
        let Y := euclideanFieldValueL3 z
        let C₀ := (eLpNorm (fieldValueArray (separatedCubicCoefficientField C)) ⊤ volume).toReal
        let C₁ := (eLpNorm (euclideanFieldGradient (separatedCubicCoefficientField C)) ⊤ volume).toReal
        let F₀ := schwartzProfileJetLInfinity 0 f
        let F₁ := schwartzProfileJetLInfinity 1 f
        let F₂ := schwartzProfileJetLInfinity 2 f
        ‖separatedModeEnergy C z f b‖ ≤
          K * D * (C₀ * F₀ * X ^ 3 + (C₀ * F₁ + C₁ * F₀) * Y * X ^ 2 + C₀ * F₂ * Y ^ 2 * X) := by
  obtain ⟨K, _, bound⟩ := separated_principal_action_derivatives_bound (J := J)
  refine ⟨K.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro b hb hom hodd D hD jet f C z hf symm hz X Y C₀ C₁ F₀ F₁ F₂
  let x := euclideanFieldGradientNorm z
  let y := eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume
  let c₀ := eLpNorm (fieldValueArray (separatedCubicCoefficientField C)) ⊤ volume
  let c₁ := eLpNorm (euclideanFieldGradient (separatedCubicCoefficientField C)) ⊤ volume
  let f₀ := eLpNorm (f : E → ℂ) ⊤ volume
  let f₁ := eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume
  let f₂ := eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume
  let rhs := K * ENNReal.ofReal D * separatedCubicBoundRhs c₀ c₁ f₀ f₁ f₂ x y
  have hFinite : rhs < ⊤ := (bound b hb hom hodd D hD jet f C z hf symm hz).1
  have hBound : ‖separatedModeEnergy C z f b‖ₑ ≤ rhs :=
    (bound b hb hom hodd D hD jet f C z hf symm hz).2.1
  have real := ENNReal.toReal_mono hFinite.ne hBound
  have eq := separated_cubic_bound_toReal c₀ c₁ f₀ f₁ f₂ x y
    (fieldValueArray_memLp _ _).eLpNorm_lt_top (euclideanFieldGradient_memLp _ _).eLpNorm_lt_top
    (f.memLp ⊤ volume).eLpNorm_lt_top ((SchwartzMap.fderivCLM ℝ f).memLp ⊤ volume).eLpNorm_lt_top
    (schwartz_profile_jet_Linfinity_lt_top 2 f) (euclideanFieldGradientNorm_lt_top z)
    (fieldValueArray_memLp z _).eLpNorm_lt_top
  rw [← ofReal_norm_eq_enorm, ENNReal.toReal_ofReal (norm_nonneg _)] at real
  change ‖separatedModeEnergy C z f b‖ ≤ rhs.toReal at real
  simp only [rhs, ENNReal.toReal_mul, ENNReal.toReal_ofReal hD, eq] at real
  change ‖separatedModeEnergy C z f b‖ ≤ K.toReal * D *
    (c₀.toReal * F₀ * x.toReal ^ 3 + (c₀.toReal * F₁ + c₁.toReal * F₀) * y.toReal * x.toReal ^ 2 +
      c₀.toReal * f₂.toReal * y.toReal ^ 2 * x.toReal)
  rw [show F₀ = f₀.toReal from schwartz_profile_jet_Linfinity_zero f,
    show F₁ = f₁.toReal from schwartz_profile_jet_Linfinity_one f]
  exact real

end Burnett.A03
