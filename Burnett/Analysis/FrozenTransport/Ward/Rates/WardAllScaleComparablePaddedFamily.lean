import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.C02

open Set Metric MeasureTheory Burnett.A02.FrequencySplit
open Burnett.A05 Burnett.A05.BoxFourier Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps (comparableSlotWeight)
open scoped ContDiff

open private wardContinuousOn_frequencyJet from Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScaleUniformChartBudget
open private wardComparablePaddedSymbol wardComparableWindow wardComparableBump_smooth wardSignedThird_smooth wardComparableNearAxis wardComparableNearAxis_open wardComparableNearAxis_of_not_mem wardComparableBump_zero wardComparablePaddedSymbol_agrees wardComparableSymbol_eq wardExtendedTriadSymbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

theorem wardComparablePaddedFamily_smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : Set X) (hV : IsOpen V) (F : X × Joint → ℂ) (hF : ContDiffOn ℝ ∞ F (V ×ˢ wardTriadDomain))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (κ : ℝ) (hκ : 0 < κ) :
    ContDiffOn ℝ ∞ (fun x : X × Joint => wardComparablePaddedSymbol ϑ κ (fun y => F (x.1,y)) x.2)
      (V ×ˢ (univ : Set Joint)) := by
  classical
  let P (x : X × Joint) := wardComparablePaddedSymbol ϑ κ (fun y => F (x.1,y)) x.2
  have hCutoff : ContDiffOn ℝ ∞ (fun x : Joint => (comparableSlotWeight ϑ κ x.1 x.2 (wardSignedThird x) : ℂ)) wardTriadDomain := by
    apply (wardComparableSymbol_smooth ϑ hϑ κ hκ.ne' (fun _ => 1) contDiffOn_const).congr
    intro x hx
    rw [wardComparableSymbol_eq, wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ hx, mul_one]
  have hWindow : ContDiff ℝ ∞ (wardComparableWindow κ) :=
    (((wardComparableBump_smooth κ).comp contDiff_fst).mul ((wardComparableBump_smooth κ).comp contDiff_snd)).mul
      ((wardComparableBump_smooth κ).comp wardSignedThird_smooth)
  have hInner : ContDiffOn ℝ ∞ P (V ×ˢ wardTriadDomain) := by
    have hMap : MapsTo (fun x : X × Joint => x.2) (V ×ˢ wardTriadDomain) wardTriadDomain :=
      fun _ hx => hx.2
    have hs := hCutoff.comp contDiff_snd.contDiffOn hMap
    have hW : ContDiffOn ℝ ∞ (fun x : X × Joint => (wardComparableWindow κ x.2 : ℂ)) (V ×ˢ wardTriadDomain) :=
      (Complex.ofRealCLM.contDiff.comp (hWindow.comp contDiff_snd)).contDiffOn
    apply (hW.mul (hs.mul hF)).congr
    intro p hp
    change P p = _
    unfold P wardComparablePaddedSymbol
    rw [wardComparableSymbol_eq, wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ hp.2]
    rfl
  have hNear : ContDiffOn ℝ ∞ P (V ×ˢ wardComparableNearAxis κ) := by
    apply (contDiffOn_const (c := (0 : ℂ))).congr
    intro p hp
    have hzero : wardComparableWindow κ p.2 = 0 := by
      rcases hp.2 with h | h | h
      · simp only [wardComparableWindow, wardComparableBump_zero κ hκ _ h.le, zero_mul]
      · simp only [wardComparableWindow, wardComparableBump_zero κ hκ _ h.le, mul_zero, zero_mul]
      · simp only [wardComparableWindow, wardComparableBump_zero κ hκ _ h.le, mul_zero]
    unfold P wardComparablePaddedSymbol
    rw [hzero, Complex.ofReal_zero, zero_mul]
  intro p hp
  by_cases hx : p.2 ∈ wardTriadDomain
  · exact (hInner.contDiffAt ((hV.prod wardTriadDomain_open).mem_nhds ⟨hp.1,hx⟩)).contDiffWithinAt
  · exact (hNear.contDiffAt ((hV.prod (wardComparableNearAxis_open κ)).mem_nhds
      ⟨hp.1,wardComparableNearAxis_of_not_mem κ hκ hx⟩)).contDiffWithinAt

end Burnett.C02
