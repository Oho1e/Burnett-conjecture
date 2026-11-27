import Burnett.Analysis.PrincipalEnergy.Freezing.CompactScalarWeylTest
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedWeylSymbolFreezeEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedInfraredCubicCoefficients

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open Filter Function MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.V03
open scoped BigOperators ContDiff ENNReal Topology

open private principal_variation_density_integrable from Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

/-- The three actual real test placements in the principal cubic polynomial. -/
def realPrincipalVariation {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ) (z : J → SchwartzMap E ℂ)
    (w : J → E → ℂ) : ℝ :=
  ∫ x, (principalVariationDensity (fun a d i j k x => (C a d i j k x : ℂ)) z w x).re

private def compactRealSchwartz (f : E → ℝ) (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f) :
    SchwartzMap E ℂ := (hc.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp hf)

private theorem principal_variation_sub_of_smooth_test {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℂ) (z : J → SchwartzMap E ℂ)
    (u v : J → E → ℂ) (hu : ∀ i, Differentiable ℝ (u i)) (hv : ∀ i, Differentiable ℝ (v i)) :
    principalVariationDensity C z (u - v) = principalVariationDensity C z u - principalVariationDensity C z v := by
  funext x
  have derivSub (i : J) (a : Index) : fderiv ℝ (u i - v i) x (EuclideanSpace.single a 1) =
      fderiv ℝ (u i) x (EuclideanSpace.single a 1) - fderiv ℝ (v i) x (EuclideanSpace.single a 1) := by
    rw [fderiv_sub (hu i x) (hv i x), ContinuousLinearMap.sub_apply]
  simp only [principalVariationDensity, Pi.sub_apply, derivSub, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem norm_real_principal_variation_sub_le {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → SchwartzMap E ℂ) (z : J → SchwartzMap E ℂ)
    (u v : J → SchwartzMap E ℂ) :
    ‖(∫ x, (principalVariationDensity (fun a d i j k => C a d i j k) z (fun i => u i) x).re) -
      (∫ x, (principalVariationDensity (fun a d i j k => C a d i j k) z (fun i => v i) x).re)‖ₑ ≤
      ‖∫ x, principalVariationDensity (fun a d i j k => C a d i j k) z
        (fun i x => u i x - v i x) x‖ₑ := by
  let U := principalVariationDensity (fun a d i j k => C a d i j k) z (fun i => u i)
  let V := principalVariationDensity (fun a d i j k => C a d i j k) z (fun i => v i)
  have hu : Integrable U := principal_variation_density_integrable C z _
    (fun i => schwartz_bounded_coordinate_jet (u i))
  have hv : Integrable V := principal_variation_density_integrable C z _
    (fun i => schwartz_bounded_coordinate_jet (v i))
  change ‖(∫ x, (U x).re) - (∫ x, (V x).re)‖ₑ ≤ _
  have had := principal_variation_sub_of_smooth_test (fun a d i j k => C a d i j k) z
    (fun i => u i) (fun i => v i) (fun i => (u i).differentiable) (fun i => (v i).differentiable)
  change principalVariationDensity (fun a d i j k => C a d i j k) z (fun i x => u i x - v i x) = U - V at had
  rw [had]
  change ‖(∫ x, (U x).re) - (∫ x, (V x).re)‖ₑ ≤ ‖∫ x, (U - V) x‖ₑ
  have hU : (∫ x, (U x).re) = (∫ x, U x).re := integral_re hu
  have hV : (∫ x, (V x).re) = (∫ x, V x).re := integral_re hv
  have hSub : (∫ x, (U - V) x) = (∫ x, U x) - ∫ x, V x := integral_sub hu hv
  rw [hU, hV, ← Complex.sub_re, hSub, ← ofReal_norm, ← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal (Complex.abs_re_le_norm _)

/-- Quantitative principal freezing from a uniform local order-zero comparison. -/
theorem exists_general_principal_freezing_bound_of_comparison {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hSmooth : ∀ a d i j k, ContDiff ℝ ∞ (C a d i j k))
    (hCompact : ∀ a d i j k, HasCompactSupport (C a d i j k))
    (hSymm : ∀ a d i j k, C a d i j k = C d a i k j)
    (R L M : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hGrad : ∀ a d i j k x, ‖fderiv ℝ (C a d i j k) x‖ ≤ L)
    (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (a β : E → E → ℝ) (K : Set E) (hK : IsCompact K)
    (hβ : ContDiff ℝ ∞ (uncurry β)) (hOff : ∀ x ∉ K, ∀ ξ, β x ξ = 0)
    (hHigh : ∀ x ξ, 1 < ‖ξ‖ → β x ξ = a x ξ)
    (hOdd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (cut : SchwartzMap E ℂ) (hCut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (CJet : ℝ) (hCJet : 0 ≤ CJet)
    (hSphere : ∀ c : E, ContDiffOn ℝ ∞ (a c) {ξ | ξ ≠ 0} ∧
      ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (a c) ξ‖ ≤ CJet)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ) (B₀ : E → SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB₀ : ∀ c u, (B₀ c u : E → ℂ) = radianAction (fixedInfraredSymbol cut 0 (a c)) u)
    (comparison : ∀ (Θ : SchwartzMap E ℂ) (θ : E → SchwartzMap E ℂ) (ℓ : ℝ), 0 < ℓ →
      (∀ c x, θ c x = Θ (ℓ⁻¹ • (x - c))) →
      ∃ D : ℝ≥0∞, D < ⊤ ∧ ∀ c : E, SchwartzOrderZeroJetBound (fun u => (-Complex.I) •
        (sandwichedScalarTest (θ c) (fun v => (B v : E → ℂ) - (B₀ c v : E → ℂ)) u -
          radianLeftQuantization (localizedFrozenPrincipalSymbol a c (θ c)) u)) D D) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∃ D : ℝ≥0∞, D < ⊤ ∧
      ∀ (c : E) (z : RealEnergyField J), tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        let X := euclideanFieldGradientNorm z.val
        let Y := eLpNorm (fieldValueArray z.val) (ENNReal.ofReal 3) volume
        let w (i : J) (x : E) := (-Complex.I) * B (z.val i) x
        let w₀ (i : J) (x : E) := (-Complex.I) * B₀ c (z.val i) x
        ‖realPrincipalVariation C z.val w - realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val w₀‖ₑ ≤
          A * ENNReal.ofReal ℓ * X ^ 3 + D * Y * X ^ 2 := by
  obtain ⟨A₁, D₁, hA₁, hD₁, coefficientBound⟩ := Burnett.V03.Palatini.exists_fixedInfrared_coefficient_freezing_bound
    C hSmooth hSymm R L M hR hL hGrad hValue cut hCut CJet hCJet
  obtain ⟨φ, _, hφ, hφc, _, windows, _⟩ := exists_nested_localized_coefficient_difference R hR.le
  let Θ := compactRealSchwartz φ hφ hφc
  let η (c : E) (s : ℝ) : SchwartzMap E ℂ :=
    if hs : 0 < s then compactRealSchwartz (fun x => φ (s⁻¹ • (x - c)))
      (windows c s hs).1 (windows c s hs).2.1 else 0
  have hη (c : E) (s : ℝ) (x : E) (hs : 0 < s) : η c s x = (φ (s⁻¹ • (x - c)) : ℂ) := by
    dsimp only [η]
    rw [dif_pos hs]
    rfl
  have hSupp : tsupport φ ⊆ closedBall (0 : E) (R + 2) := by
    have h := (windows 0 1 one_pos).2.2.2.1
    simpa only [inv_one, sub_zero, one_smul, mul_one] using h.trans ball_subset_closedBall
  let S (a d : Index) (i j k : J) := compactRealSchwartz (C a d i j k) (hSmooth a d i j k) (hCompact a d i j k)
  have hS (a d : Index) (i j k : J) (x : E) : S a d i j k x = (C a d i j k x : ℂ) := rfl
  have hSize (a d : Index) (i j k : J) : eLpNorm (S a d i j k : E → ℂ) ⊤ volume ≤ ENNReal.ofReal M := by
    rw [eLpNorm_exponent_top]
    apply eLpNormEssSup_le_of_ae_bound
    exact Eventually.of_forall fun x => by rw [hS, Complex.norm_real]; exact hValue a d i j k x
  have remainder (s : ℝ) (hs : 0 < s) :=
    comparison Θ (fun c => η c s) s hs (fun c x => hη c s x hs)
  obtain ⟨A₂, hA₂, testBound⟩ := exists_localizedWeyl_frozen_symbol_energy_bound S
    (fun a d i j k => by simp only [S, hSymm a d i j k]) (ENNReal.ofReal M) ENNReal.ofReal_lt_top hSize
    a β K hK hβ hOff hHigh hOdd (fun x t ht ξ => hHom t ht x ξ)
    φ hφ (R + 2) (R + 3) R (by linarith) (by linarith) (by linarith) hR hSupp
    η hη (fun u => (B u : E → ℂ)) (fun c u => (B₀ c u : E → ℂ)) remainder
  refine ⟨A₁ + ENNReal.ofReal A₂, ENNReal.add_lt_top.mpr ⟨hA₁, ENNReal.ofReal_lt_top⟩, ?_⟩
  intro ℓ hℓ hℓ₁
  obtain ⟨D₂, hD₂, testEstimate⟩ := testBound ℓ hℓ hℓ₁
  refine ⟨D₁ + D₂, ENNReal.add_lt_top.mpr ⟨hD₁, hD₂⟩, ?_⟩
  intro c z hz X Y w w₀
  let χ := η c ℓ
  let win (i : J) := (-Complex.I) • energyProduct χ
    (B (energyProduct χ (z.val i)) - B₀ c (energyProduct χ (z.val i)))
  have winAction (i : J) (x : E) : win i x = (-Complex.I) *
      sandwichedScalarTest χ (fun v => (B v : E → ℂ) - (B₀ c v : E → ℂ)) (z.val i) x := by
    simp only [win, SchwartzMap.smul_apply, smul_eq_mul, energyProduct_apply, SchwartzMap.sub_apply,
      sandwichedScalarTest, Pi.sub_apply]
  have centerSupport (i : J) : tsupport (z.val i : E → ℂ) ⊆ ball c (R * ℓ) := by
    apply (closure_mono ?_).trans hz
    intro x hx
    change z.val i x ≠ 0 at hx
    change fieldValueArray z.val x ≠ 0
    intro he
    exact hx (congrArg (fun w => w i) he)
  have χone (x : E) (hx : x ∈ ball c (R * ℓ)) : χ x = 1 := by
    have hBall : x ∈ closedBall c ((R + 1) * ℓ) :=
      (ball_subset_closedBall.trans (closedBall_subset_closedBall (by nlinarith))) hx
    have one : φ (ℓ⁻¹ • (x - c)) = 1 := (windows c ℓ hℓ).2.2.1 x hBall
    rw [hη c ℓ x hℓ, one, Complex.ofReal_one]
  let U (i : J) : SchwartzMap E ℂ := (-Complex.I) • B (z.val i)
  let V (i : J) : SchwartzMap E ℂ := (-Complex.I) • B₀ c (z.val i)
  let Q (u : SchwartzMap E ℂ) (x : E) := (-Complex.I) * (B u x - B₀ c u x)
  have localized (i : J) : (win i : E → ℂ) = sandwichedScalarTest χ Q (z.val i) := by
    funext x
    rw [winAction i x]
    simp only [sandwichedScalarTest, Pi.sub_apply, Q]
    ring
  have raw (i : J) : Q (z.val i) = fun x => U i x - V i x := by
    funext x
    simp only [U, V, Q, SchwartzMap.smul_apply, smul_eq_mul, mul_sub]
  have hEnergy := testEstimate c z.val z.property hz win winAction
  rw [principalPatchTestEnergy, (principal_variation_action_derivatives S z.val (fun i => win i)
    (fun i => schwartz_bounded_coordinate_jet (win i))).1.deriv] at hEnergy
  have hWindow := principal_variation_integral_sandwiched_test (fun a d i j k => S a d i j k)
    z.val Q χ (ball c (R * ℓ)) isOpen_ball centerSupport χone
  simp only [localized] at hEnergy
  rw [hWindow] at hEnergy
  simp only [raw] at hEnergy
  have hLeading : ENNReal.ofReal (A₂ * ℓ * euclideanFieldGradientL3 z.val ^ 3) =
      ENNReal.ofReal A₂ * ENNReal.ofReal ℓ * X ^ 3 := by
    rw [ENNReal.ofReal_mul (mul_nonneg hA₂ hℓ.le), ENNReal.ofReal_mul hA₂, euclideanFieldGradientL3,
      ENNReal.ofReal_pow ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (euclideanFieldGradientNorm_lt_top z.val).ne]
  rw [hLeading] at hEnergy
  have hTest : ‖realPrincipalVariation C z.val w - realPrincipalVariation C z.val w₀‖ₑ ≤
      ENNReal.ofReal A₂ * ENNReal.ofReal ℓ * X ^ 3 + D₂ * Y * X ^ 2 := by
    have h := norm_real_principal_variation_sub_le S z.val U V
    simpa only [realPrincipalVariation, hS, w, w₀, U, V, SchwartzMap.smul_apply, smul_eq_mul] using h.trans hEnergy
  have hCoefficient := (coefficientBound c (a c) (hSphere c).1 (fun t ht ξ => hHom t ht c ξ) (hOdd c) (hSphere c).2 ℓ hℓ z hz).2.2
  have hFrozen : ‖realPrincipalVariation C z.val w₀ -
      realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val w₀‖ₑ ≤
      A₁ * ENNReal.ofReal ℓ * X ^ 3 + D₁ * Y * X ^ 2 := by
    simpa only [realPrincipalVariation, w₀, hB₀] using hCoefficient
  let x := realPrincipalVariation C z.val w
  let y := realPrincipalVariation C z.val w₀
  let t := realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val w₀
  change ‖x - t‖ₑ ≤ _
  rw [show x - t = (x - y) + (y - t) by ring]
  exact ((enorm_add_le _ _).trans (add_le_add hTest hFrozen)).trans_eq (by ring)

/-- Joint test and coefficient freezing for every finite field, using a
represented full Weyl action and the same fixed infrared convention. -/
theorem exists_general_principal_freezing_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hSmooth : ∀ a d i j k, ContDiff ℝ ∞ (C a d i j k))
    (hCompact : ∀ a d i j k, HasCompactSupport (C a d i j k))
    (hSymm : ∀ a d i j k, C a d i j k = C d a i k j)
    (R L M : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hGrad : ∀ a d i j k x, ‖fderiv ℝ (C a d i j k) x‖ ≤ L)
    (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (test : CompactScalarWeylTest)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ) (B₀ : E → SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u, (B u : E → ℂ) = test.action u)
    (hB₀ : ∀ c u, (B₀ c u : E → ℂ) = test.frozenAction c u) :
    ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∃ D : ℝ≥0∞, D < ⊤ ∧
      ∀ (c : E) (z : RealEnergyField J), tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        let X := euclideanFieldGradientNorm z.val
        let Y := eLpNorm (fieldValueArray z.val) (ENNReal.ofReal 3) volume
        let w (i : J) (x : E) := (-Complex.I) * B (z.val i) x
        let w₀ (i : J) (x : E) := (-Complex.I) * B₀ c (z.val i) x
        ‖realPrincipalVariation C z.val w - realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val w₀‖ₑ ≤
          A * ENNReal.ofReal ℓ * X ^ 3 + D * Y * X ^ 2 := by
  obtain ⟨CJet, hCJet, hSphere⟩ := test.principal_sphere_jets
  refine exists_general_principal_freezing_bound_of_comparison C hSmooth hCompact hSymm R L M
    hR hL hGrad hValue test.principal test.regularizedPrincipal _ (isCompact_closedBall _ _)
    test.regularizedSmooth test.regularizedPrincipal_support test.regularizedPrincipal_high
    test.principalOdd test.principalHomogeneous test.infraredCutoff test.infraredReal
    CJet hCJet hSphere B B₀ hB₀ ?_
  intro Θ θ ℓ hℓ hShape
  simpa only [hB, hB₀] using test.exists_center_uniform_order_zero_remainder Θ θ ℓ hℓ hShape

end Burnett.A03
