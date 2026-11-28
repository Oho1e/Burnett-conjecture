import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleComparableBoxFamily
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps (comparableSlotWeight)
open scoped ContDiff

open private wardContinuousOn_frequencyJet from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
open private wardComparablePaddedSymbol wardComparableWindow wardComparableBump_smooth wardSignedThird_smooth wardComparableNearAxis wardComparableNearAxis_open wardComparableNearAxis_of_not_mem wardComparableBump_zero wardComparablePaddedSymbol_agrees wardComparableSymbol_eq wardExtendedTriadSymbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

/-- The same finite relative shifts used in the actual comparable triad
have a single compact-family L³ trilinear bound. -/
theorem exists_wardComparableForm_compactFamilyBound {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (K V : Set X) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (F : X × Joint → ℂ) (hF : ContDiffOn ℝ ∞ F (V ×ˢ wardTriadDomain))
    (hHom : ∀ c ∈ K, ∀ t : ℝ, 0 < t → ∀ x ∈ wardTriadDomain, F (c,t • x) = F (c,x))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c ∈ K, ∀ f g h : SchwartzMap E ℂ,
      ‖radianTrilinearForm (wardComparableSymbol ϑ κ (fun x => F (c,x))) f g h‖ ≤
        C * (triLpMass f g h 3 3 3).toReal := by
  classical
  obtain ⟨N,C,hC,hBound⟩ := exists_radianComparable_box_bound hCut hFlat 5 κ 1 1
    (by norm_num) hκ hSmall zero_lt_one zero_lt_one
  let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let A := ContinuousLinearEquiv.refl ℝ E
  let G := wardComparableBoxFamily ϑ κ F
  obtain ⟨B,hB,hJets⟩ := exists_wardComparableBoxFamily_jetBound K V hK hV hKV F hF ϑ hϑ κ hκ I
  refine ⟨C * B, mul_nonneg hC hB,?_⟩
  intro c hc
  let M := fun x => F (c,x)
  let m := wardComparableSymbol ϑ κ M
  have hM : ContDiffOn ℝ ∞ M wardTriadDomain :=
    hF.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => ⟨hKV hc,hx⟩)
  have hm : Measurable m := measurable_radianFourBranchSymbol ϑ hϑ.continuous.measurable κ _
    ((hM.continuousOn.measurable_piecewise continuousOn_const wardTriadDomain_open.measurableSet)) 3
  have homExt (t : ℝ) (ht : 0 < t) (x : Joint) :
      wardExtendedTriadSymbol M (t • x) = wardExtendedTriadSymbol M x := by
    have he : t • x ∈ wardTriadDomain ↔ x ∈ wardTriadDomain := by
      simp only [wardTriadDomain, mem_setOf_eq, wardSignedThird, Prod.smul_fst, Prod.smul_snd,
        ← smul_add, ← smul_neg, smul_ne_zero_iff_right ht.ne']
    by_cases hx : x ∈ wardTriadDomain
    · rw [wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ (he.mpr hx), piecewise_eq_of_mem _ _ _ hx]
      exact hHom c hc t ht x hx
    · rw [wardExtendedTriadSymbol, piecewise_eq_of_notMem _ _ _ (mt he.mp hx), piecewise_eq_of_notMem _ _ _ hx]
      rfl
  have hHomM : ∀ t : ℝ, 0 < t → ∀ x : Joint, m (t • x) = m x :=
    radianFourBranchSymbol_homogeneous ϑ κ (wardExtendedTriadSymbol M) homExt 3
  have hs (x : Joint) (hx : m x ≠ 0) : comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) ≠ 0 := by
    intro h
    apply hx
    change wardComparableSymbol ϑ κ M x = 0
    rw [wardComparableSymbol_eq, h, Complex.ofReal_zero, zero_mul]
  have hGSmooth (k : ℤ) (hk : k ∈ I) : ContDiff ℝ ∞ (fun x => G k (c,x)) :=
    (hJets c hc k hk).1
  have hGJet (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40) (x : BoxSpace) (hx : x ∈ ball 0 5) :
      ‖iteratedFDeriv ℝ n (fun y => G k (c,y)) x‖ ≤ B :=
    (hJets c hc k hk).2 n hn x hx
  have hMatch (k : ℤ) (_ : k ∈ I) (ζ υ : E) (_ : endpointHighProfile ζ ≠ 0) (hυ : endpointHighProfile υ ≠ 0) :
      G k (c,joinedInputs ζ υ) = m ((2 : ℝ)^k • ζ, υ) := by
    simp only [G, wardComparableBoxFamily, boxToPair_joined]
    exact wardComparablePaddedSymbol_agrees ϑ hCut hFlat κ hκ hSmall M _ (endpointHighProfile_properties.2.2 υ hυ).1.le
  refine hBound A m ?_ hHomM hm.aestronglyMeasurable (fun k x => G k (c,x)) B hB
    (fun k hk => ((hGSmooth k hk).of_le (WithTop.coe_le_coe.mpr le_top)).contDiffOn) hGJet hMatch
  intro x hx
  simpa only [A, ContinuousLinearEquiv.refl_apply, one_mul, le_refl, and_self, and_true, wardSignedThird] using hs x hx

end Burnett.C02
