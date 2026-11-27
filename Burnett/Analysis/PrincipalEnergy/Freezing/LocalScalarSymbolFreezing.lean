import Burnett.Analysis.PrincipalEnergy.Freezing.LocalCubicTestAgreement
import Burnett.Analysis.PrincipalEnergy.Freezing.FixedInfraredReality
import Burnett.Analysis.PrincipalEnergy.Freezing.FrozenOrderOneSchwartzAction

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open Filter Function MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ContDiff ComplexConjugate ENNReal Topology

open private fixed_radian_profile_smooth from Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

/-- A compact homogeneous principal symbol has the angular and mixed
seminorms used by the two freezing estimates. -/
theorem compact_local_principal_symbol_data (a : E → E → ℝ) (Rb : ℝ)
    (hSmooth : ContDiffOn ℝ ∞ (uncurry a) {p : E × E | p.2 ≠ 0})
    (hSupport : ∀ x ξ, x ∉ closedBall (0 : E) Rb → a x ξ = 0)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (cut : SchwartzMap E ℂ)
    (hLow : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile cut ξ = 1)
    (hHigh : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0) :
    let β := fun x => fixedInfraredSymbol cut 0 (a x)
    ContDiff ℝ ∞ (uncurry β) ∧
    CompactBaseFrequencyJets (fun x ξ => (a x ξ : ℂ)) {ξ | ξ ≠ 0} ∧
    (∃ M : ℝ, 0 ≤ M ∧ CompactBaseOrderOneBudget a M) ∧
    ∃ J : ℝ, 0 ≤ J ∧ ∀ c, ContDiffOn ℝ ∞ (a c) {ξ | ξ ≠ 0} ∧
      ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n (a c) ξ‖ ≤ J := by
  intro β
  have hZero (ξ : E) : fixedRadianProfile (0 : SchwartzMap E ℂ) ξ = 0 := by simp [fixedRadianProfile]
  have hβ : ContDiff ℝ ∞ (uncurry β) := by
    rw [contDiff_iff_contDiffAt]
    intro p
    by_cases h : p.2 = 0
    · have hNear : ∀ᶠ q : E × E in 𝓝 p, fixedRadianProfile cut q.2 = 1 :=
        (continuous_snd.tendsto p).eventually (by simpa only [h] using hLow)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hNear] with q hq
      change fixedInfraredSymbol cut 0 (a q.1) q.2 = 0
      rw [fixedInfraredSymbol, hq, sub_self, zero_mul, zero_add, hZero]
    · have hOpen : IsOpen {q : E × E | q.2 ≠ 0} := isOpen_ne.preimage continuous_snd
      have hRegular : ContDiffAt ℝ ∞ (fun q : E × E => fixedRadianProfile cut q.2) p :=
        (fixed_radian_profile_smooth cut).contDiffAt.comp p contDiffAt_snd
      change ContDiffAt ℝ ∞ (fun q : E × E => fixedInfraredSymbol cut 0 (a q.1) q.2) p
      simpa only [fixedInfraredSymbol, hZero, add_zero, uncurry] using
        ((contDiffAt_const (c := (1 : ℝ))).sub hRegular).mul
          (hSmooth.contDiffAt (hOpen.mem_nhds h))
  have hOff (x : E) (hx : x ∉ closedBall (0 : E) Rb) (ξ : E) : β x ξ = 0 := by
    simp [β, fixedInfraredSymbol, hSupport x ξ hx, fixedRadianProfile]
  have hMatch (x ξ : E) (hξ : 1 < ‖ξ‖) : β x ξ = a x ξ :=
    fixedInfraredSymbol_outside cut 0 (a x) ξ (hHigh ξ hξ) (by simp [fixedRadianProfile])
  let aC := fun x ξ => (a x ξ : ℂ)
  let βC := fun x ξ => (β x ξ : ℂ)
  have hβC : ContDiff ℝ ∞ (uncurry βC) := Complex.ofRealCLM.contDiff.comp hβ
  have hOffC (x : E) (hx : x ∉ closedBall (0 : E) Rb) (ξ : E) : βC x ξ = 0 := by
    simp [βC, hOff x hx ξ]
  have hMatchC (x ξ : E) (hξ : 1 < ‖ξ‖) : βC x ξ = aC x ξ :=
    congrArg Complex.ofReal (hMatch x ξ hξ)
  have hHomC (x : E) (t : ℝ) (ht : 0 < t) (ξ : E) : aC x (t • ξ) = t • aC x ξ := by
    simp only [aC, hHom t ht x ξ, Complex.ofReal_mul, Complex.real_smul]
  have ha := Burnett.V03.compact_homogeneous_symbol_punctured_jets aC βC hβC hMatchC hHomC
  obtain ⟨U, _, sphereU, _, _, _, budget⟩ := Burnett.V03.compact_homogeneous_symbol_mixed_jet_budget
    aC βC (closedBall (0 : E) Rb) (isCompact_closedBall _ _) hβC hOffC hMatchC hHomC
  obtain ⟨M, hM, mode⟩ := budget 7 8
  obtain ⟨V, _, sphereV, _, _, _, angular⟩ := Burnett.V03.compact_homogeneous_symbol_mixed_jet_budget
    a β (closedBall (0 : E) Rb) (isCompact_closedBall _ _) hβ hOff hMatch
      (fun x t ht ξ => hHom t ht x ξ)
  obtain ⟨J, hJ, jet⟩ := angular 16 0
  refine ⟨hβ, ha, ⟨M,hM,?_⟩, J,hJ,?_⟩
  · intro n hn ξ hξ x
    exact ⟨by simpa only [norm_iteratedFDeriv_zero] using mode n hn 0 (by decide) x ξ (sphereU hξ),
      mode n hn 8 le_rfl x ξ (sphereU hξ)⟩
  · intro c
    refine ⟨?_, fun n hn ξ hξ => ?_⟩
    · simpa [aC] using Complex.reCLM.contDiff.comp_contDiffOn (ha.frequencySmooth c)
    · simpa only [norm_iteratedFDeriv_zero] using jet n hn 0 le_rfl c ξ (sphereV hξ)

/-- Local order-one freezing using the actual scalar test and its homogeneous
left action. A physical classical amplitude supplies the order-zero gap. -/
theorem exists_symmetric_action_freezing_of_local_left_gap
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
    (P Rb : ℝ) (hP : 0 < P) (hRP : Rb < P)
    (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ) (hρSupport : tsupport ρ ⊆ ball (0 : E) P)
    (hρOne : ∀ x ∈ closedBall (0 : E) Rb, ρ x = 1)
    (a : E → E → ℝ) (haSmooth : ContDiffOn ℝ ∞ (uncurry a) {p : E × E | p.2 ≠ 0})
    (haSupport : ∀ x ξ, x ∉ closedBall (0 : E) Rb → a x ξ = 0)
    (hOdd : ∀ x ξ, a x (-ξ) = -a x ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x ξ, a x (t • ξ) = t * a x ξ)
    (cut : SchwartzMap E ℂ) (hCut : ∀ ξ, ((cut ξ).re : ℂ) = cut ξ)
    (hEven : ∀ ξ, fixedRadianProfile cut (-ξ) = fixedRadianProfile cut ξ)
    (hLow : ∀ᶠ ξ in 𝓝 (0 : E), fixedRadianProfile cut ξ = 1)
    (hHigh : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (B BRep : SchwartzMap E ℂ → SchwartzMap E ℂ)
    (gap : ∃ D : ℝ≥0∞, D < ⊤ ∧ SchwartzOrderZeroJetBound (fun u =>
      (BRep u : E → ℂ) - radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u) D D)
    (U : Set E) (hU : IsOpen U) (hLocal : ∀ u : SchwartzMap E ℂ, tsupport (u : E → ℂ) ⊆ U →
      EqOn (fun x => B u x) (fun x => BRep u x) U)
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
  let β := fun x => fixedInfraredSymbol cut 0 (a x)
  obtain ⟨hβ, ha, ⟨Mₐ,hMₐ,budget⟩, DJet, hDJet, sphere⟩ :=
    compact_local_principal_symbol_data a Rb haSmooth haSupport hHom cut hLow hHigh
  have hMatch (x ξ : E) (hξ : 1 < ‖ξ‖) : β x ξ = a x ξ :=
    fixedInfraredSymbol_outside cut 0 (a x) ξ (hHigh ξ hξ) (by simp [fixedRadianProfile])
  have hOff (x : E) (hx : x ∉ closedBall (0 : E) Rb) (ξ : E) : β x ξ = 0 := by
    simp [β, fixedInfraredSymbol, haSupport x ξ hx, fixedRadianProfile]
  have frozen (c : E) := exists_order_one_frozen_schwartz_action (a c) (β c) (sphere c).1
    (hβ.comp (contDiff_const.prodMk contDiff_id)) (fun t ht ξ => hHom t ht c ξ) (hMatch c)
  choose B₀ hB₀ using frozen
  refine ⟨B₀,hB₀,?_⟩
  intro hFrozenReal
  let F (u : SchwartzMap E ℂ) := ((BRep u : E → ℂ) - radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u)
  have split (u : SchwartzMap E ℂ) :
      (BRep u : E → ℂ) = radianLeftQuantization (fun x ξ => (a x ξ : ℂ)) u + F u := by
    dsimp only [F]
    abel
  obtain ⟨D, hD, hF⟩ := gap
  have zeroReal (ξ : E) : (((0 : SchwartzMap E ℂ) ξ).re : ℂ) = (0 : SchwartzMap E ℂ) ξ := by simp
  have principal := exists_general_principal_freezing_bound_of_comparison C hSmooth hCompact hSymm R L M
    hR hL hGrad hValue a β _ (isCompact_closedBall _ _) hβ hOff hMatch hOdd hHom cut hCut
    DJet hDJet sphere BRep B₀ hB₀ (fun Θ θ ℓ hℓ hShape => by
      simpa only [hB₀] using exists_affine_original_test_comparison_W13
        P Rb hP hRP ρ hρ hρSupport hρOne a haSupport ha hHom Mₐ hMₐ budget
        (fun u => (BRep u : E → ℂ)) F split D D hD hD hF cut 0 hCut zeroReal Θ θ ℓ hℓ hShape)
  have values := CompactScalarWeylTest.exists_action_value_L3_bound_of_left_gap
    P Rb hP hRP ρ hρ hρSupport hρOne a haSupport ha hHom Mₐ hMₐ budget BRep ⟨D,hD,hF⟩
  obtain ⟨A,hA,estimate⟩ :=
    exists_general_complete_cubic_freezing_bound_of_scalar_bounds C C₀ C₁ R hR BRep B₀ principal values
  have hMeas (a d : Index) (i j k : J) : Measurable (C a d i j k) := (hSmooth a d i j k).continuous.measurable
  refine ⟨A,hA,?_⟩
  intro ℓ hℓ hℓle
  obtain ⟨Dℓ,hDℓ,hEstimate⟩ := estimate ℓ hℓ (hℓle.trans hℓ₀)
  refine ⟨Dℓ,hDℓ,?_⟩
  intro c z hPatch hz
  have hSupport (i : J) : tsupport (z.val i : E → ℂ) ⊆ U := by
    apply (closure_mono ?_).trans (hz.trans hPatch)
    intro x hx
    change z.val i x ≠ 0 at hx
    change fieldValueArray z.val x ≠ 0
    intro h
    exact hx (congrArg (fun v => v i) h)
  let w (i : J) := (-Complex.I) • BRep (z.val i)
  have hAgreement (i : J) :
      EqOn (fun x => (realSkewCubicTest B hReal z).val i x) (fun x => w i x) U := by
    intro x hx
    simp only [realSkewCubicTest, w, SchwartzMap.smul_apply, smul_eq_mul,
      hLocal (z.val i) (hSupport i) hx]
  rw [symmetricAction_test_of_diagonal C hMeas M hValue C₀ C₁ T hDiag z,
    symmetricFrozenAction_test_of_diagonal C c M (fun a d i j k => hValue a d i j k c) (T₀ c) (hFrozenDiag c) z,
    realCompleteCubicTest_eq_of_local_test_agreement C C₀ C₁ z.val (realSkewCubicTest B hReal z).val w hU
      hSupport hAgreement]
  exact hEstimate c z hz

end Burnett.A03
