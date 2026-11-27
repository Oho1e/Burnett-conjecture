import Burnett.Analysis.PrincipalEnergy.Freezing.LocalScalarSymbolFreezing
import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalAmplitudePrincipalComparison
import Burnett.Analysis.PrincipalEnergy.Freezing.ClassicalAmplitudeWeakRepresentation

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open Filter Function MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ContDiff ComplexConjugate ENNReal Topology

/-- Quantitative freezing for an actual locally represented classical scalar
test. The physical two-point quantization determines the order-zero gap,
and the fixed infrared convention determines the frozen action. -/
theorem exists_symmetric_action_freezing_of_local_classical_amplitude
    {J : Type} [Fintype J] (C : Index → Index → J → J → J → E → ℝ)
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
    (P Rb Ry H : ℝ) (hP : 0 < P) (hRP : Rb < P) (hH : 1 ≤ H)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρSupport : tsupport ρ ⊆ ball (0 : E) P)
    (hρOne : ∀ x ∈ closedBall (0 : E) Rb, ρ x = 1)
    (A : E → E → E → ℂ) (hA : CompactRadianTwoPointOrderOne A Rb Ry)
    (directions : RadianOrdinaryDirectionalAmplitudeBounds A)
    (a : E → E → ℝ)
    (haSmooth : ContDiffOn ℝ ∞ (fun p : E × E => (a p.1 p.2 : ℂ)) radianPuncturedSymbolDomain)
    (haSupport : ∀ x ξ, x ∉ closedBall (0 : E) Rb → a x ξ = 0)
    (hOdd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (tail : RadianOrderZeroSymbolTail H (fun x ξ => A x x ξ - (a x ξ : ℂ)))
    (cut : SchwartzMap E ℂ) (hCut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hEven : ∀ ξ, fixedRadianProfile cut (-ξ) = fixedRadianProfile cut ξ)
    (hLow : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile cut ξ = 1)
    (hHigh : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (K : E → E → ℂ) (RK : ℝ) (hK : ContDiff ℝ 1 (uncurry K))
    (hKSupport : ∀ x y, x ∉ closedBall (0 : E) RK ∨ y ∉ closedBall (0 : E) RK → K x y = 0)
    (κ : ℕ → SchwartzMap E ℂ) (hκBound : ∀ n ξ, ‖κ n ξ‖ ≤ 1)
    (hκLimit : ∀ ξ, Tendsto (fun n => κ n ξ) atTop (𝓝 1))
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ) (outer : SchwartzMap E ℂ)
    (representation : ∀ (u v : SchwartzMap E ℂ),
      Tendsto (fun n => weylLebesguePairing (radianTwoPointCutoffAction A (κ n) u) v) atTop
        (𝓝 (weylLebesguePairing
          (sandwichedScalarTest outer (fun w => (B w : E → ℂ)) u - compactKernelAction K u) v)))
    (U : Set E) (hU : IsOpen U) (hOuter : ∀ x ∈ U, outer x = 1)
    (hReal : ∀ u : SchwartzMap E ℂ, (∀ x, conj (u x) = u x) →
      ∀ x, conj ((-Complex.I) * B u x) = (-Complex.I) * B u x) :
    ∃ (B₀ : E → SchwartzMap E ℂ → SchwartzMap E ℂ)
      (hB₀ : ∀ c u, (B₀ c u : E → ℂ) = radianAction (fixedInfraredSymbol cut 0 (a c)) u),
      let hFrozenReal : ∀ c (u : SchwartzMap E ℂ), (∀ x, conj (u x) = u x) →
        ∀ x, conj ((-Complex.I) * B₀ c u x) = (-Complex.I) * B₀ c u x := fun c u hu x => by
          rw [congrFun (hB₀ c u) x]
          exact radianSkewAction_fixedInfrared_preserves_real cut hEven (a c) (hOdd c) u hu x
      ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ ℓ₀ → ∃ D : ℝ, 0 ≤ D ∧
        ∀ (c : E) (z : RealEnergyField J), ball c (R * ℓ) ⊆ U → tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
          |T.action z z (realSkewCubicTest B hReal z) -
            (T₀ c).action z z (realSkewCubicTest (B₀ c) (hFrozenReal c) z)| ≤
            A * ℓ * euclideanFieldGradientL3 z.val ^ 3 +
            D * euclideanFieldValueL3 z.val * euclideanFieldGradientL3 z.val ^ 2 := by
  let BRep := fun u => energyProduct outer (B (energyProduct outer u))
  have hRep (u : SchwartzMap E ℂ) : (BRep u : E → ℂ) =
      sandwichedScalarTest outer (fun w => (B w : E → ℂ)) u := by
    funext x
    simp [BRep, energyProduct_apply, sandwichedScalarTest]
  have action : (fun u => (BRep u : E → ℂ)) = compactRadianAmplitudeTestAction A Rb Ry hA K := by
    apply compact_radian_amplitude_test_eq_of_pairing_limit A Rb Ry hA K RK hK hKSupport κ hκBound hκLimit
      (fun u => (BRep u : E → ℂ)) (fun u => (BRep u).continuous)
    simpa only [hRep] using representation
  have hRealSmooth : ContDiffOn ℝ ∞ (uncurry a) {p : E × E | p.2 ≠ 0} := by
    have domain : {p : E × E | p.2 ≠ 0} = radianPuncturedSymbolDomain := by
      ext p
      simp [radianPuncturedSymbolDomain]
    have unwrap : Complex.reCLM ∘ (fun p : E × E => (a p.1 p.2 : ℂ)) = uncurry a := by
      funext p
      exact Complex.ofReal_re _
    rw [domain]
    simpa only [unwrap] using Complex.reCLM.contDiff.comp_contDiffOn haSmooth
  obtain ⟨_, ha, ⟨Mₐ, hMₐ, budget⟩, _⟩ :=
    compact_local_principal_symbol_data a Rb hRealSmooth haSupport hHom cut hLow hHigh
  have hOutside (ξ : E) (hξ : H < ‖ξ‖) : fixedRadianProfile cut ξ = 0 := hHigh ξ (hH.trans_lt hξ)
  have gap : ∃ D : ℝ≥0∞, D < ⊤ ∧ SchwartzOrderZeroJetBound (fun u =>
      (BRep u : E → ℂ) - radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u) D D := by
    simpa only [congrFun action] using exists_compact_classical_amplitude_homogeneous_difference_W13
      P Rb Ry H hP hRP ρ hρ hρSupport hρOne A hA directions a haSmooth haSupport tail ha hHom
      Mₐ hMₐ budget cut hCut hLow hOutside K RK hK hKSupport
  have hLocal : ∀ u : SchwartzMap E ℂ, tsupport (u : E → ℂ) ⊆ U →
      EqOn (fun x => B u x) (fun x => BRep u x) U := by
    intro u hu x hx
    have input : energyProduct outer u = u := by
      ext y
      rw [energyProduct_apply]
      by_cases hy : y ∈ U
      · rw [hOuter y hy, one_mul]
      · have hz : u y = 0 := by
          by_contra hn
          exact hy (hu (subset_tsupport (f := (u : E → ℂ)) hn))
        rw [hz, mul_zero]
    simp [BRep, energyProduct_apply, input, hOuter x hx]
  exact exists_symmetric_action_freezing_of_local_left_gap C hSmooth hCompact hSymm C₀ C₁
    T T₀ hDiag hFrozenDiag R L M ℓ₀ hR hL hℓ₀ hGrad hValue P Rb hP hRP ρ hρ hρSupport
    hρOne a hRealSmooth haSupport hOdd hHom cut hCut hEven hLow hHigh B BRep gap U hU hLocal hReal

end Burnett.A03
