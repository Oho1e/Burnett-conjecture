import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformPhaseComponents
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleLowProfileFamilies
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleComparableProfileFamilies
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorBranchBounds
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePhase
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 20000000

noncomputable section

namespace Burnett.C02

open Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.A05
open Burnett.P01 (ComplexComponents)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff

open private wardLowGaugeMiddleSymbol_eq_phase from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePhase
open private wardComparableDenominator from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableFactors

/-- A bound uniform in the frozen center for each genuine ordered
phase-component symbol. -/
def WardFamilyComponentBounds (K : Set E) (m : E → Tensor2) (physical : Fin 3 → Bool)
    (A : (Fin 3 → OrderedPair) → E → Joint → ℂ) : Prop :=
  ∀ k, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ K, WardActualLowComponentBound (m x) physical k (A k x) C

private theorem wardTestSlice_smooth (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) (c : E) :
    ContDiffOn ℝ ∞ (fun ξ => a (c,ξ)) {ξ : E | ξ ≠ 0} :=
  ha.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hx => hx)

private theorem wardLowPhaseRatio_jointSmooth (V : Set E) :
    ContDiffOn ℝ ∞ (fun x : E × WardLowPoint => (x.2.2.2 : ℂ)) (V ×ˢ wardLowProfileDomain) :=
  (Complex.ofRealCLM.contDiff.comp contDiff_snd.snd.snd).contDiffOn

/-- All low and comparable physical-phase component bounds are uniform
over the compact receiving-center family, including the middle term. -/
theorem wardActualPhaseComponents_compactFamilyUniform
    (K V : Set E) (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V)
    (m : E → Tensor2) (w : E → ℝ) (hm : ∀ a b, ContDiffOn ℝ ∞ (fun x => m x a b) V)
    (hw : ContDiffOn ℝ ∞ w V)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0})
    (hOdd : ∀ x ξ, a (x,-ξ) = -a (x,ξ))
    (hHom : ∀ x (t : ℝ), 0 < t → ∀ ξ, a (x,t • ξ) = t * a (x,ξ))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1)
    (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16) :
    let H (k : Fin 3 → OrderedPair) (j : Fin 3) := wardTensorBasis (k j)
    let test (x : E) (ξ : E) := a (x,ξ)
    WardFamilyComponentBounds K m ![false,true,true] (fun k x =>
      wardLowGaugeMiddleSymbol ϑ κ (m x) (w x) (test x) (H k 0) (H k 1) (H k 2)) ∧
    WardFamilyComponentBounds K m ![false,true,true] (fun k x =>
      wardActualLowCut ϑ κ (wardOneLowGaugeLieRaw (m x) (w x) (test x) (H k 0) (H k 1) (H k 2))) ∧
    WardFamilyComponentBounds K m ![true,true,false] (fun k x =>
      wardActualLowCut ϑ κ (wardOneHighGaugeRaw (m x) (w x) (test x) (H k 2) (H k 0) (H k 1))) ∧
    WardFamilyComponentBounds K m ![true,false,false] (fun k x =>
      wardActualLowCut ϑ κ (wardTwoGaugePhysicalLowRaw (m x) (w x) (test x) (H k 1) (H k 2) (H k 0))) ∧
    WardFamilyComponentBounds K m ![false,true,false] (fun k x =>
      wardActualLowCut ϑ κ (wardTwoGaugeGaugeLowRaw (m x) (w x) (test x) (H k 0) (H k 2) (H k 1))) ∧
    WardFamilyComponentBounds K m ![true,true,false] (fun k x =>
      wardComparableSymbol ϑ κ (wardOneHighGaugeRaw (m x) (w x) (test x) (H k 2) (H k 0) (H k 1))) ∧
    WardFamilyComponentBounds K m ![true,false,false] (fun k x =>
      wardComparableSymbol ϑ κ (wardTwoGaugePhysicalLowRaw (m x) (w x) (test x) (H k 1) (H k 2) (H k 0))) := by
  classical
  intro H test
  have hLow (k l j : ComplexComponents) := wardLowPhaseProfiles_jointSmooth V m w hm hw a ha k l j
  have hComp (k l j : ComplexComponents) := wardComparablePhaseProfiles_jointSmooth V m w hm hw a ha k l j
  have hRatio := wardLowPhaseRatio_jointSmooth V
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    let F (p : E × WardLowPoint) := lowGaugeScalarPhaseProfiles (m p.1) (w p.1) (test p.1) (H k 0) (H k 1) (H k 2) p.2
    let f (j : Fin 2) (p : E × WardLowPoint) := ![(F p).1,(F p).2] j
    have hf (j : Fin 2) : ContDiffOn ℝ ∞ (f j) (V ×ˢ wardLowProfileDomain) := by
      fin_cases j
      · exact (hLow (H k 0) (H k 1) (H k 2)).1.fst
      · exact (hLow (H k 0) (H k 1) (H k 2)).1.snd
    choose C hC hEst using fun j => exists_wardLowRadialForm_compactFamilyBound K V hK hV hKV (f j) (hf j)
      ϑ hϑ hCut κ hκ hSmall
    refine ⟨64 * ∑ j, C j, mul_nonneg (by norm_num) (Finset.sum_nonneg fun j _ => hC j), ?_⟩
    intro c hc
    refine wardActualPhaseComponent_bound_of_radial (m c)
      (wardLowGaugeMiddleSymbol ϑ κ (m c) (w c) (test c) (H k 0) (H k 1) (H k 2))
      (fun j => wardLowRadialSymbol ϑ κ (fun y => f j (c,y))) C hC ![1,2] ![false,true,true] k
      (by intro j; fin_cases j <;> rfl) (fun j => hEst j c hc) ?_
    intro x
    change _ = ∑ j : Fin 2, _
    rw [Fin.sum_univ_two]
    exact wardLowGaugeMiddleSymbol_eq_phase ϑ hCut κ hκ hSmall (m c) (w c) (test c)
      (wardTestSlice_smooth a ha c) (hOdd c) (hHom c) (H k 0) (H k 1) (H k 2) x
  · intro k
    let F (j : Fin 2) (p : E × WardLowPoint) := wardOneLowGaugeLieProfiles (m p.1) (w p.1) (test p.1)
      (H k 0) (H k 1) (H k 2) j p.2
    have hF (j : Fin 2) : ContDiffOn ℝ ∞ (F j) (V ×ˢ wardLowProfileDomain) := by
      fin_cases j
      · exact (hLow (H k 0) (H k 1) (H k 2)).2.1.fst
      · exact (hLow (H k 0) (H k 1) (H k 2)).2.1.snd
    exact exists_wardActualLowComponent_compactFamilyBound K V hK hV hKV ϑ hϑ hCut κ hκ hSmall m
      (fun c => wardOneLowGaugeLieRaw (m c) (w c) (test c) (H k 0) (H k 1) (H k 2)) F hF
      ![1,2] ![false,true,true] k (by intro j; fin_cases j <;> rfl) (fun c _ =>
        wardOneLowGaugeLieRaw_normalized (m c) (w c) (test c) (wardTestSlice_smooth a ha c)
          (hOdd c) (hHom c) (H k 0) (H k 1) (H k 2))
  · intro k
    let F (j : Fin 2) (p : E × WardLowPoint) := wardOneHighGaugeProfiles (m p.1) (w p.1) (test p.1)
      (H k 2) (H k 0) (H k 1) j p.2
    have hF (j : Fin 2) : ContDiffOn ℝ ∞ (F j) (V ×ˢ wardLowProfileDomain) := by
      fin_cases j
      · exact (hLow (H k 2) (H k 0) (H k 1)).2.2.1.fst.mul (hRatio.pow 2)
      · exact (hLow (H k 2) (H k 0) (H k 1)).2.2.1.snd.mul hRatio
    exact exists_wardActualLowComponent_compactFamilyBound K V hK hV hKV ϑ hϑ hCut κ hκ hSmall m
      (fun c => wardOneHighGaugeRaw (m c) (w c) (test c) (H k 2) (H k 0) (H k 1)) F hF
      ![0,1] ![true,true,false] k (by intro j; fin_cases j <;> rfl) (fun c _ =>
        wardOneHighGaugeRaw_normalized (m c) (w c) (test c) (wardTestSlice_smooth a ha c)
          (hOdd c) (hHom c) (H k 2) (H k 0) (H k 1))
  · intro k
    let F (_ : Fin 1) (p : E × WardLowPoint) := wardTwoGaugePhysicalLowProfile (m p.1) (w p.1) (test p.1)
      (H k 1) (H k 2) (H k 0) p.2
    have hF (j : Fin 1) : ContDiffOn ℝ ∞ (F j) (V ×ˢ wardLowProfileDomain) :=
      (hLow (H k 1) (H k 2) (H k 0)).2.2.2.fst.mul (hRatio.pow 2)
    refine exists_wardActualLowComponent_compactFamilyBound K V hK hV hKV ϑ hϑ hCut κ hκ hSmall m
      (fun c => wardTwoGaugePhysicalLowRaw (m c) (w c) (test c) (H k 1) (H k 2) (H k 0)) F hF
      (fun _ => 0) ![true,false,false] k (fun _ => rfl) ?_
    intro c hc x hx
    simpa only [Fin.sum_univ_one, wardPhaseCovector, Matrix.cons_val_zero] using
      (wardTwoGaugeLowRaw_normalized (m c) (w c) (test c) (wardTestSlice_smooth a ha c)
        (hOdd c) (hHom c) (H k 1) (H k 2) (H k 0) x hx).1
  · intro k
    let F (_ : Fin 1) (p : E × WardLowPoint) := wardTwoGaugeGaugeLowProfile (m p.1) (w p.1) (test p.1)
      (H k 0) (H k 2) (H k 1) p.2
    have hF (j : Fin 1) : ContDiffOn ℝ ∞ (F j) (V ×ˢ wardLowProfileDomain) :=
      (hLow (H k 0) (H k 2) (H k 1)).2.2.2.snd.mul hRatio
    refine exists_wardActualLowComponent_compactFamilyBound K V hK hV hKV ϑ hϑ hCut κ hκ hSmall m
      (fun c => wardTwoGaugeGaugeLowRaw (m c) (w c) (test c) (H k 0) (H k 2) (H k 1)) F hF
      (fun _ => 1) ![false,true,false] k (fun _ => rfl) ?_
    intro c hc x hx
    simpa only [Fin.sum_univ_one, wardPhaseCovector, Matrix.cons_val_one, Matrix.cons_val_zero] using
      (wardTwoGaugeLowRaw_normalized (m c) (w c) (test c) (wardTestSlice_smooth a ha c)
        (hOdd c) (hHom c) (H k 0) (H k 2) (H k 1) x hx).2
  · intro k
    let F (j : Fin 2) (p : E × Joint) := wardComparableOneGaugeProfiles (m p.1) (w p.1) (test p.1)
      (H k 2) (H k 0) (H k 1) j p.2
    refine exists_wardActualComparableComponent_compactFamilyBound K V hK hV hKV ϑ hϑ hCut hFlat κ hκ hSmall m
      (fun c => wardOneHighGaugeRaw (m c) (w c) (test c) (H k 2) (H k 0) (H k 1)) F
      (hComp (H k 2) (H k 0) (H k 1)).1 (fun j c _ =>
        (wardComparableOneGaugeProfiles_smooth_hom (m c) (w c) (test c) (H k 2) (H k 0) (H k 1)
          (wardTestSlice_smooth a ha c) (hHom c) j).2)
      ![0,1] ![true,true,false] k (by intro j; fin_cases j <;> rfl) (fun c _ =>
        wardComparableOneGaugeRaw_normalized (m c) (w c) (test c) (H k 2) (H k 0) (H k 1))
  · intro k
    let F (_ : Fin 1) (p : E × Joint) := wardComparableTwoGaugeProfile (m p.1) (w p.1) (test p.1)
      (H k 1) (H k 2) (H k 0) p.2
    refine exists_wardActualComparableComponent_compactFamilyBound K V hK hV hKV ϑ hϑ hCut hFlat κ hκ hSmall m
      (fun c => wardTwoGaugePhysicalLowRaw (m c) (w c) (test c) (H k 1) (H k 2) (H k 0)) F
      (fun _ => (hComp (H k 1) (H k 2) (H k 0)).2) (fun _ c _ =>
        (wardComparableTwoGaugeProfile_smooth_hom (m c) (w c) (test c) (H k 1) (H k 2) (H k 0)
          (wardTestSlice_smooth a ha c) (hHom c)).2)
      (fun _ => 0) ![true,false,false] k (fun _ => rfl) ?_
    intro c hc x hx
    simpa only [Fin.sum_univ_one, wardPhaseCovector, Matrix.cons_val_zero] using
      wardComparableTwoGaugeRaw_normalized (m c) (w c) (test c) (H k 1) (H k 2) (H k 0) x hx

end Burnett.C02
