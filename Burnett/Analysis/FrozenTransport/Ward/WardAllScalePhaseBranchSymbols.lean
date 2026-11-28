import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowCut
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeLiePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.C02

open Set Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ComplexComponents ComplexCovector)
open Burnett.V08 (signedCyclicPhase normalizedGaugePotential)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped ContDiff

open private wardGaugePotentialAt from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

/-- Last two terms of the exact low gauge identity on the original signed
triad before moving the physical phases to their corresponding fields. -/
def wardOneLowGaugeLieRaw (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents) (x : Joint) : ℂ :=
  let r := -(x.1 + x.2)
  let v := wardGaugePotentialAt x.1 G
  (-2 : ℂ) * (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) *
    ((quadratic m x.2 : ℂ) * wardScreenLieContraction m H J v x.1 +
      (quadratic m r : ℂ) * wardScreenLieContraction m J H v x.1)

def wardOneLowGaugeLieProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (i : Fin 2) (x : WardLowPoint) : ℂ :=
  ![(lowGaugeLiePhaseProfiles m w a G H J x).1, (lowGaugeLiePhaseProfiles m w a G H J x).2] i

theorem wardOneLowGaugeLieProfiles_smooth (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G H J : ComplexComponents) (i : Fin 2) :
    ContDiffOn ℝ ∞ (wardOneLowGaugeLieProfiles m w a G H J i) wardLowProfileDomain := by
  have h := lowGaugeLiePhaseProfiles_contDiffOn m w a ha G H J
  fin_cases i
  · exact h.fst
  · exact h.snd

theorem wardOneLowGaugeLieRaw_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) (G H J : ComplexComponents)
    (x : Joint) (hx : x ∈ wardLowActive) :
    wardOneLowGaugeLieRaw m w a G H J x = ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ) *
      ∑ i : Fin 2, wardOneLowGaugeLieProfiles m w a G H J i (wardLowInput x) *
        (normalizedFrozenPhase m (wardPhaseCovector x (![1,2] i)) : ℂ) := by
  have h := lowGaugeLiePhase_eq_normalized m w a ha hOdd hHom x.1 x.2 hx.1 hx.2.1
    (hx.2.2.trans (by norm_num)) G H J
  have he := (div_eq_iff (wardLowActive_radialProduct_ne_zero hx)).mp h
  rw [mul_comm]
  simpa [wardOneLowGaugeLieRaw, wardOneLowGaugeLieProfiles, wardLowInput, wardPhaseCovector, Fin.sum_univ_two] using he

/-- The one-high-gauge expression with two physical phases, before applying
the actual first-low partition. The gauge is the signed third frequency. -/
def wardOneHighGaugeRaw (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents) (x : Joint) : ℂ :=
  let r := -(x.1 + x.2)
  let v : ComplexCovector := fun i => (‖r‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection r) G i
  let pair := frozenWardScreenPair m H J
  (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) *
    ((quadratic m x.1 : ℂ) * wardHighGaugeBracket m pair H J v x.2 +
      (quadratic m x.2 : ℂ) * wardHighGaugeBracket m pair J H v x.1)

def wardOneHighGaugeProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (i : Fin 2) (x : WardLowPoint) : ℂ :=
  ![(highGaugePhaseProfiles m w a G H J x).1 * (x.2.2 : ℂ)^2,
    (highGaugePhaseProfiles m w a G H J x).2 * (x.2.2 : ℂ)] i

private theorem wardPhaseRatio_smooth : ContDiff ℝ ∞ (fun x : WardLowPoint => (x.2.2 : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp contDiff_snd.snd

theorem wardOneHighGaugeProfiles_smooth (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G H J : ComplexComponents) (i : Fin 2) :
    ContDiffOn ℝ ∞ (wardOneHighGaugeProfiles m w a G H J i) wardLowProfileDomain := by
  have h := highGaugePhaseProfiles_contDiffOn m w a ha G H J
  fin_cases i
  · exact h.fst.mul (wardPhaseRatio_smooth.pow 2).contDiffOn
  · exact h.snd.mul wardPhaseRatio_smooth.contDiffOn

theorem wardOneHighGaugeRaw_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) (G H J : ComplexComponents)
    (x : Joint) (hx : x ∈ wardLowActive) :
    wardOneHighGaugeRaw m w a G H J x = ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ) *
      ∑ i : Fin 2, wardOneHighGaugeProfiles m w a G H J i (wardLowInput x) *
        (normalizedFrozenPhase m (wardPhaseCovector x (![0,1] i)) : ℂ) := by
  have h := highGaugePhase_eq_normalized m w a ha hOdd hHom x.1 x.2 hx.1 hx.2.1
    (hx.2.2.trans (by norm_num)) G H J
  have he := (div_eq_iff (wardLowActive_radialProduct_ne_zero hx)).mp h
  rw [mul_comm]
  simpa [wardOneHighGaugeRaw, wardOneHighGaugeProfiles, wardLowInput, wardPhaseCovector, Fin.sum_univ_two] using he

/-- Two-gauge raw expression with low physical slot first and gauge slots
second and signed third. -/
def wardTwoGaugePhysicalLowRaw (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents) (x : Joint) : ℂ :=
  (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.1 : ℂ) *
    wardTwoGaugeBracket m H (wardGaugePotentialAt (-(x.1+x.2)) G₂) (wardGaugePotentialAt x.2 G₁) x.2

/-- Two-gauge raw expression with a low gauge first, physical second and
the other gauge in the signed third slot. -/
def wardTwoGaugeGaugeLowRaw (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents) (x : Joint) : ℂ :=
  (signedCyclicPhase a x.1 x.2 : ℂ) * (w : ℂ) * (quadratic m x.2 : ℂ) *
    wardTwoGaugeBracket m H (wardGaugePotentialAt (-(x.1+x.2)) G₂) (wardGaugePotentialAt x.1 G₁) x.1

def wardTwoGaugePhysicalLowProfile (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents)
    (x : WardLowPoint) : ℂ := (twoGaugePhaseProfiles m w a G₁ G₂ H x).1 * (x.2.2 : ℂ)^2

def wardTwoGaugeGaugeLowProfile (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents)
    (x : WardLowPoint) : ℂ := (twoGaugePhaseProfiles m w a G₁ G₂ H x).2 * (x.2.2 : ℂ)

theorem wardTwoGaugeLowProfiles_smooth (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G₁ G₂ H : ComplexComponents) :
    ContDiffOn ℝ ∞ (wardTwoGaugePhysicalLowProfile m w a G₁ G₂ H) wardLowProfileDomain ∧
      ContDiffOn ℝ ∞ (wardTwoGaugeGaugeLowProfile m w a G₁ G₂ H) wardLowProfileDomain := by
  have h := twoGaugePhaseProfiles_contDiffOn m w a ha G₁ G₂ H
  exact ⟨h.fst.mul (wardPhaseRatio_smooth.pow 2).contDiffOn, h.snd.mul wardPhaseRatio_smooth.contDiffOn⟩

theorem wardTwoGaugeLowRaw_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ) (G₁ G₂ H : ComplexComponents)
    (x : Joint) (hx : x ∈ wardLowActive) :
    let D := ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ)
    (wardTwoGaugePhysicalLowRaw m w a G₁ G₂ H x = D *
      (wardTwoGaugePhysicalLowProfile m w a G₁ G₂ H (wardLowInput x) * (normalizedFrozenPhase m x.1 : ℂ))) ∧
    (wardTwoGaugeGaugeLowRaw m w a G₁ G₂ H x = D *
      (wardTwoGaugeGaugeLowProfile m w a G₁ G₂ H (wardLowInput x) * (normalizedFrozenPhase m x.2 : ℂ))) := by
  intro D
  have h := twoGaugePhase_eq_normalized m w a ha hOdd hHom x.1 x.2 hx.1 hx.2.1
    (hx.2.2.trans (by norm_num)) G₁ G₂ H
  have hn := wardLowActive_radialProduct_ne_zero hx
  constructor
  · rw [mul_comm D]
    exact (div_eq_iff hn).mp h.1
  · rw [mul_comm D]
    exact (div_eq_iff hn).mp h.2

end Burnett.C02
