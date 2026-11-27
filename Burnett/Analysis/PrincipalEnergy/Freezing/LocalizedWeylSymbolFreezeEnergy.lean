import Burnett.Analysis.TransportWard.Weyl.CompactPrincipalJets
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedLeftPrincipalFreezing
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedWeylPrincipalFreezing

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.V03

open Filter Function MeasureTheory Metric Set Burnett.A03 Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ComplexConjugate ContDiff ENNReal Topology

/-- In the actual localized variable-minus-frozen Weyl test, the
order-one part costs one power of the patch size. The genuine
order-zero correction costs one undifferentiated field factor. -/
theorem exists_localizedWeyl_frozen_symbol_energy_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ)
    (hSymm : ∀ a b i j k, C a b i j k = C b a i k j)
    (C₀ : ℝ≥0∞) (hCfin : C₀ < ⊤)
    (hC : ∀ a b i j k, eLpNorm (C a b i j k : E → ℂ) ⊤ volume ≤ C₀)
    (a β : E → E → ℝ) (K : Set E) (hK : IsCompact K)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (hOff : ∀ x ∉ K, ∀ ξ, β x ξ = 0)
    (hHigh : ∀ x ξ, 1 < ‖ξ‖ → β x ξ = a x ξ)
    (hOdd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a x (t • ξ) = t * a x ξ)
    (φ : E → ℝ) (hφ : ContDiff ℝ ∞ φ) (S P R : ℝ)
    (hS : 0 ≤ S) (hP : 0 < P) (hSP : S < P) (hR : 0 < R)
    (hφS : tsupport φ ⊆ closedBall (0 : E) S)
    (η : E → ℝ → SchwartzMap E ℂ)
    (hη : ∀ c ℓ x, 0 < ℓ → η c ℓ x = (φ (ℓ⁻¹ • (x - c)) : ℂ))
    (B : SchwartzMap E ℂ → E → ℂ) (B₀ : E → SchwartzMap E ℂ → E → ℂ)
    (hRem : ∀ ℓ : ℝ, 0 < ℓ → ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ c : E,
      SchwartzOrderZeroJetBound
        (fun u => (-Complex.I) •
          (sandwichedScalarTest (η c ℓ) (fun v => B v - B₀ c v) u -
            radianLeftQuantization (localizedFrozenPrincipalSymbol a c (η c ℓ)) u)) D D) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ (c : E) (z : J → SchwartzMap E ℂ),
        (∀ i x, conj (z i x) = z i x) →
        tsupport (fieldValueArray z) ⊆ ball c (R * ℓ) →
        ∀ w : J → SchwartzMap E ℂ,
        (∀ i x, w i x = (-Complex.I) * sandwichedScalarTest (η c ℓ) (fun v => B v - B₀ c v) (z i) x) →
        ‖principalPatchTestEnergy C z (fun i => w i)‖ₑ ≤
          ENNReal.ofReal (A * ℓ * euclideanFieldGradientL3 z ^ 3) +
          D * eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume * euclideanFieldGradientNorm z ^ 2 := by
  obtain ⟨U,hU,hSphere,hFreq,hBase,hMixed,hBudget⟩ :=
    compact_homogeneous_symbol_mixed_jet_budget a β K hK hβ hOff hHigh
      (fun x t ht ξ => by simpa only [smul_eq_mul] using hHom x t ht ξ)
  have hAngular (H : ℕ) : ∃ D : ℝ, 0 ≤ D ∧ SpatialAngularJetBound a univ U S 8 H D := by
    obtain ⟨D,hD,h⟩ := hBudget H 8
    refine ⟨D,hD,?_⟩
    intro c _ ξ hξ r hr j _ hj x _
    exact h r hr j (by simpa only [max_eq_right (by decide : (1 : ℕ) ≤ 8)] using hj) x ξ hξ
  obtain ⟨D,hD,hD₁₆⟩ := hAngular 16
  obtain ⟨A,L,hA,_,estimate⟩ :=
    exists_localized_left_principal_freezing_bound C hSymm φ hφ S P R hS hP hSP hR
      hφS 8 (by decide)
  refine ⟨A * D, mul_nonneg hA hD, ?_⟩
  intro ℓ hℓ hℓ₁
  obtain ⟨G,hG,comm⟩ := hRem ℓ hℓ
  let P₀ : ℝ≥0∞ := (Fintype.card ((Index × J) × (Index × J)) : ℝ≥0∞) * Fintype.card J * C₀
  let E₀ : ℝ≥0∞ := ENNReal.ofReal (L * D)
  let E₁ : ℝ≥0∞ := G + 2 * (G + G * ENNReal.ofReal (3 * (R * ℓ)))
  have hP₀ : P₀ < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) (ENNReal.natCast_lt_top _)) hCfin
  have hTwo : (2 : ℝ≥0∞) < ⊤ := by simp
  have hE₁ : E₁ < ⊤ := ENNReal.add_lt_top.mpr ⟨hG, ENNReal.mul_lt_top hTwo
    (ENNReal.add_lt_top.mpr ⟨hG, ENNReal.mul_lt_top hG ENNReal.ofReal_lt_top⟩)⟩
  refine ⟨P₀ * E₀ + P₀ * E₁, ENNReal.add_lt_top.mpr
    ⟨ENNReal.mul_lt_top hP₀ ENNReal.ofReal_lt_top, ENNReal.mul_lt_top hP₀ hE₁⟩, ?_⟩
  intro c z hz hSupport w hw
  obtain ⟨V,hV,hWeak,hEnergy⟩ := estimate a univ U hU hSphere hFreq hBase hMixed hAngular
    hOdd hHom D hD hD₁₆ c (mem_univ c) ℓ hℓ hℓ₁ C₀ hC z hz hSupport
  let M := ENNReal.ofReal (A * D * ℓ * euclideanFieldGradientL3 z ^ 3)
  let Y := eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume
  let X := euclideanFieldGradientNorm z
  have hEnergy' : ‖principalCubicLpFunctional C z V‖ₑ ≤ M + P₀ * E₀ * Y * X ^ 2 := hEnergy
  have hTest := localized_weyl_principal_freezing_of_left_bound C z B (B₀ c) a c (η c ℓ)
    (fun x => φ (ℓ⁻¹ • (x - c))) (fun x => hη c ℓ x hℓ) R ℓ hR hℓ hSupport
    C₀ hC G (M + P₀ * E₀ * Y * X ^ 2) (comm c) V hV hWeak hEnergy' w hw
  change ‖principalPatchTestEnergy C z (fun i => w i)‖ₑ ≤ M + (P₀ * E₀ + P₀ * E₁) * Y * X ^ 2
  calc
    _ ≤ M + P₀ * E₀ * Y * X ^ 2 + P₀ * E₁ * Y * X ^ 2 := hTest
    _ = _ := by ring

end Burnett.V03
