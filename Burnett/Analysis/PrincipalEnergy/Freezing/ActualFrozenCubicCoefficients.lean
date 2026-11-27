import Burnett.Analysis.PrincipalEnergy.Freezing.FrozenCoefficientPrincipalEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.SharedLocalizedCoefficient

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview
open scoped ContDiff ENNReal Topology BigOperators ComplexConjugate Burnett.A03

private theorem norm_fderiv_one_jet {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (x : E) : ‖fderiv ℝ f x‖ = ‖iteratedFDeriv ℝ 1 f x‖ := by
  simpa only [norm_iteratedFDeriv_zero, zero_add] using
    (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := f) (x := x) (n := 0))

/-- The shared smooth cutoff gives the literal coefficient difference
and the cubic freezing bound uniformly in the patch center and scale. -/
theorem exists_actual_frozen_cubic_coefficient_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hSmooth : ∀ a b i j k, ContDiff ℝ ∞ (C a b i j k))
    (hSymm : ∀ a b i j k, C a b i j k = C b a i k j)
    (R L : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hGrad : ∀ a b i j k x, ‖fderiv ℝ (C a b i j k) x‖ ≤ L) :
    ∃ (φ : E → ℝ) (A : ℝ≥0∞), ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ A < ⊤ ∧
      ∀ (c : E) (ℓ : ℝ), 0 < ℓ →
        let θ (x : E) := φ (ℓ⁻¹ • (x - c))
        (∀ x ∈ closedBall c ((R + 1) * ℓ), θ x = 1) ∧
        ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
          (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
          (∀ ξ, b (-ξ) = -b ξ) → ∀ D : ℝ, 0 ≤ D →
          (∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
          ∀ z : J → SchwartzMap E ℂ, (∀ j x, conj (z j x) = z j x) →
            tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
            let w (i : J) := radianSkewAction b (z i)
            let Cvar a b i j k x := (C a b i j k x : ℂ)
            let Cc a b i j k (_ : E) := (C a b i j k c : ℂ)
            ‖∫ x, principalVariationDensity Cvar z w x - principalVariationDensity Cc z w x‖ₑ ≤
              A * ENNReal.ofReal D * ENNReal.ofReal ℓ * euclideanFieldGradientNorm z ^ 3 := by
  obtain ⟨φ, Q, hφ, hφc, hQ, scaled, _⟩ := exists_nested_localized_coefficient_difference R hR.le
  obtain ⟨K, hK, freeze⟩ := exists_frozen_coefficient_principal_energy_bound (J := J)
  let U := ENNReal.ofReal (L * (R + 2))
  let B := ENNReal.ofReal ((1 + (R + 2) * Q) * L)
  let P := ENNReal.ofReal (3 * R)
  let V := ENNReal.ofReal Q
  let T := U + (U * V + B) * P + U * V * P ^ 2
  have hT : T < ⊤ := by
    dsimp only [T]
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top,
      ENNReal.mul_lt_top (ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top,
        ENNReal.ofReal_lt_top⟩) ENNReal.ofReal_lt_top⟩,
      ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top) (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)⟩
  refine ⟨φ, K * T, hφ, hφc, ENNReal.mul_lt_top hK hT, ?_⟩
  intro c ℓ hℓ θ
  obtain ⟨hθ, hθc, one, _, _, _, hθJet, difference⟩ := scaled c ℓ hℓ
  refine ⟨one, ?_⟩
  intro b hb hom odd D hD hJets z hReal hz w Cvar Cc
  let F (x : E) := (θ x : ℂ)
  have hF : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp hθ
  let f : SchwartzMap E ℂ := (hθc.comp_left Complex.ofReal_zero).toSchwartzMap hF
  have hf : ∀ x, f x = F x := fun _ => rfl
  let d₀ (a b : Index) (i j k : J) := localizedCoefficientDifference θ (C a b i j k) c
  have bound (a b : Index) (i j k : J) :=
    difference (C a b i j k) (hSmooth a b i j k) L hL (fun x _ => hGrad a b i j k x)
  let d (a b : Index) (i j k : J) : SchwartzMap E ℂ :=
    ((bound a b i j k).2.1.comp_left Complex.ofReal_zero).toSchwartzMap
      (Complex.ofRealCLM.contDiff.comp (bound a b i j k).1)
  have hSame (a b : Index) (i j k : J) (x : E) : d a b i j k x = (d₀ a b i j k x : ℂ) := rfl
  have hSymD (a b : Index) (i j k : J) : d a b i j k = d b a i k j := by
    ext x
    simp only [hSame, d₀, hSymm a b i j k]
  have hPlateau (x : E) (hx : x ∈ ball c (R * ℓ)) : x ∈ closedBall c ((R + 1) * ℓ) :=
    (ball_subset_closedBall.trans (closedBall_subset_closedBall (by nlinarith))) hx
  have hDifference (a b : Index) (i j k : J) (x : E) (hx : x ∈ ball c (R * ℓ)) :
      d a b i j k x = Cvar a b i j k x - Cc a b i j k x := by
    have hEq : d₀ a b i j k x = C a b i j k x - C a b i j k c :=
      (bound a b i j k).2.2.2.1 x (hPlateau x hx)
    rw [hSame, hEq]
    exact Complex.ofReal_sub _ _
  have hVal (a b : Index) (i j k : J) : eLpNorm (d a b i j k : E → ℂ) ⊤ volume ≤ U * ENNReal.ofReal ℓ := by
    rw [eLpNorm_exponent_top]
    have hnorm : ENNReal.ofReal (L * ((R + 2) * ℓ)) = U * ENNReal.ofReal ℓ := by
      rw [← mul_assoc, ENNReal.ofReal_mul (by positivity : 0 ≤ L * (R + 2))]
    rw [← hnorm]
    apply eLpNormEssSup_le_of_ae_bound
    exact Eventually.of_forall fun x => by
      rw [hSame, Complex.norm_real]
      exact ((bound a b i j k).2.2.2.2.1 x).1
  have hDval (a b : Index) (i j k : J) (l : Index) :
      eLpNorm (energyPartial l (d a b i j k) : E → ℂ) ⊤ volume ≤ B := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    refine Eventually.of_forall fun x => ?_
    have hOp : ‖fderiv ℝ (d a b i j k : E → ℂ) x‖ = ‖fderiv ℝ (d₀ a b i j k) x‖ := by
      rw [norm_fderiv_one_jet, norm_fderiv_one_jet]
      exact Complex.ofRealLI.norm_iteratedFDeriv_comp_left (bound a b i j k).1.contDiffAt (by simp)
    change ‖fderiv ℝ (d a b i j k : E → ℂ) x (EuclideanSpace.single l 1)‖ ≤ (1 + (R + 2) * Q) * L
    refine ((fderiv ℝ (d a b i j k : E → ℂ) x).le_opNorm _).trans ?_
    rw [show ‖EuclideanSpace.single l (1 : ℝ)‖ = 1 by simp, mul_one, hOp]
    exact ((bound a b i j k).2.2.2.2.1 x).2
  have hF0 : eLpNorm (f : E → ℂ) ⊤ volume ≤ 1 := by
    rw [← ENNReal.ofReal_one, eLpNorm_exponent_top]
    exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => by
      rw [hf, Complex.norm_real]
      exact (hθJet x).1)
  have hF1 : eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume ≤ ENNReal.ofReal (Q / ℓ) := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    refine Eventually.of_forall fun x => ?_
    rw [norm_fderiv_one_jet]
    have heq : ‖iteratedFDeriv ℝ 1 (f : E → ℂ) x‖ = ‖iteratedFDeriv ℝ 1 θ x‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left hθ.contDiffAt (by simp)
    exact heq.trans_le (hθJet x).2.2.2.1
  have hF2 : eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume ≤ ENNReal.ofReal (Q / ℓ ^ 2) := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    refine Eventually.of_forall fun x => ?_
    have heq : ‖iteratedFDeriv ℝ 2 (f : E → ℂ) x‖ = ‖iteratedFDeriv ℝ 2 θ x‖ :=
      Complex.ofRealLI.norm_iteratedFDeriv_comp_left hθ.contDiffAt
        (WithTop.coe_le_coe.mpr (le_top : (2 : ℕ∞) ≤ ⊤))
    exact heq.trans_le (hθJet x).2.2.2.2
  have scale1 : eLpNorm (fderiv ℝ (f : E → ℂ)) ⊤ volume * ENNReal.ofReal ℓ ≤ V := by
    refine (mul_le_mul_right' hF1 _).trans_eq ?_
    rw [← ENNReal.ofReal_mul (div_nonneg hQ hℓ.le), div_mul_cancel₀ _ hℓ.ne']
  have scale2 : eLpNorm (iteratedFDeriv ℝ 2 (f : E → ℂ)) ⊤ volume * ENNReal.ofReal ℓ ^ 2 ≤ V := by
    refine (mul_le_mul_right' hF2 _).trans_eq ?_
    rw [← ENNReal.ofReal_pow hℓ.le, ← ENNReal.ofReal_mul (div_nonneg hQ (sq_nonneg ℓ)),
      div_mul_cancel₀ _ (pow_ne_zero _ hℓ.ne')]
  have hOne (x : E) (hx : x ∈ ball c (R * ℓ)) : f x = 1 := by
    have he : θ x = 1 := one x (hPlateau x hx)
    rw [hf, show F x = (θ x : ℂ) from rfl, he, Complex.ofReal_one]
  have hBound := freeze b hb hom odd D hD hJets Cvar d z f c R ℓ hR hℓ hz hOne
    (fun x => by rw [hf]; exact Complex.conj_ofReal _) hReal hSymD hDifference
    U B V V hVal hDval hF0 scale1 scale2
  exact hBound.trans_eq (by dsimp only [T]; ring)

end Burnett.A03
