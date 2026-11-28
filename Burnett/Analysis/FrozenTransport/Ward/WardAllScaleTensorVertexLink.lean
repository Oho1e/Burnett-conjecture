import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorBranchBounds
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzActualSlots
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 18000000

noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight comparableSlotWeight)
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum signedCyclicPhase)
open scoped Matrix

open private wardComparableSymbol_eq wardExtendedTriadSymbol from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleComparableTransfer

private theorem wardActualTensorWeight_eq_originalSpectra (m : Tensor2) (physical : Fin 3 → Bool)
    (A : Joint → WardTensorTrilinear) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (x : Joint) :
    wardActualTensorWeight m physical A wi wo hm hη i o z x =
      A x (fun t => if physical t then wardActualThinSpectrum m wi wo hm hη i o z (wardPhaseCovector x t)
        else originalGaugeSpectrum z (wardPhaseCovector x t)) := by
  unfold wardActualTensorWeight
  congr 1
  funext t a b
  by_cases h : physical t = true
  · simp only [wardActualLowSlots, h, if_true, wardActualThinSpectrum]
  · simp only [wardActualLowSlots, if_neg h]
    rfl

private theorem wardHighGaugeSpectra_slots (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (p q : E) :
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    (fun j : Fin 3 => if (![true,true,false] : Fin 3 → Bool) j then H (wardPhaseCovector (p,q) j)
        else originalGaugeSpectrum z (wardPhaseCovector (p,q) j)) =
      ![H p, H q, originalGaugeSpectrum z (-(p+q))] := by
  intro H
  funext j
  fin_cases j <;> rfl

/-- The exact high-gauge energy integrand is the bounded ordered tensor
form on both the first-low and the comparable sectors. -/
theorem wardActualHighGauge_cut_tensor_eq_vertex (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (p q : E) (hx : (p,q) ∈ wardTriadDomain) :
    let r := -(p+q)
    let B := inverseMatrix G
    let H := wardActualThinSpectrum B wi wo hm hη i o z
    let Γ := (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun i => p i) (H p)
      (fun i => q i) (H q) (fun i => r i) (originalGaugeSpectrum z r)
    let A := wardOneHighGaugeRawTrilinear B (metricDensity G) a
    wardActualTensorWeight B ![true,true,false] (wardFirstLowTrilinear ϑ κ A) wi wo hm hη i o z (p,q) =
      (lowSlotWeight ϑ κ p q r : ℂ) * Γ ∧
    wardActualTensorWeight B ![true,true,false] (wardComparableTrilinear ϑ κ A) wi wo hm hη i o z (p,q) =
      (comparableSlotWeight ϑ κ p q r : ℂ) * Γ := by
  classical
  intro r B H Γ A
  have hSym : IsSymmetricTensor B := by
    change IsSymmetricTensor (inverseMatrix G)
    rw [← f.inverseMetric_eq]
    exact TensorFrame.inverseMetric_symmetric f.components
  have hx' : p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 := hx
  have hv := wardActualHighGaugeRaw_eq_vertex G hG hg f a wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx'.2.2
  let u : Fin 3 → ComplexComponents := ![H p, H q, originalGaugeSpectrum z r]
  have hApply : A (p,q) u = Γ := by
    rw [wardOneHighGaugeRawTrilinear_apply _ _ _ _ _ hSym]
    exact hv.symm
  constructor
  · rw [wardActualTensorWeight_eq_originalSpectra, wardHighGaugeSpectra_slots, wardFirstLowTrilinear_apply,
      wardActualLowCut, if_pos ⟨hx'.1,hx'.2.1⟩]
    change _ * A (p,q) u = _
    rw [hApply]
  · rw [wardActualTensorWeight_eq_originalSpectra, wardHighGaugeSpectra_slots, wardComparableTrilinear_apply,
      wardComparableSymbol_eq, wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ hx]
    change _ * A (p,q) u = _
    rw [hApply]
    rfl


section TwoGauge

variable (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (p q : E)

include hG hg f hi hio hSmall hWindow hz

theorem wardActualTwoGauge_physical_cut_tensor_eq_vertex (hx : (p,q) ∈ wardTriadDomain) :
    let r := -(p+q)
    let B := inverseMatrix G
    let H := wardActualThinSpectrum B wi wo hm hη i o z
    let Γ := (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun i => p i) (H p)
      (fun i => q i) (originalGaugeSpectrum z q) (fun i => r i) (originalGaugeSpectrum z r)
    let A := wardTwoGaugePhysicalRawTrilinear B (metricDensity G) a
    wardActualTensorWeight B ![true,false,false] (wardFirstLowTrilinear ϑ κ A) wi wo hm hη i o z (p,q) =
      (lowSlotWeight ϑ κ p q r : ℂ) * Γ ∧
    wardActualTensorWeight B ![true,false,false] (wardComparableTrilinear ϑ κ A) wi wo hm hη i o z (p,q) =
      (comparableSlotWeight ϑ κ p q r : ℂ) * Γ := by
  classical
  intro r B H Γ A
  have hx' : p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 := hx
  let u : Fin 3 → ComplexComponents := ![H p, originalGaugeSpectrum z q, originalGaugeSpectrum z r]
  have hSlots : (fun j : Fin 3 => if (![true,false,false] : Fin 3 → Bool) j then H (wardPhaseCovector (p,q) j)
      else originalGaugeSpectrum z (wardPhaseCovector (p,q) j)) = u := by
    funext j
    fin_cases j <;> rfl
  have hv := wardActualTwoGaugePhysicalRaw_eq_vertex G hG hg f a wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx'.2.1 hx'.2.2
  have hApply : A (p,q) u = Γ := by
    rw [wardTwoGaugePhysicalRawTrilinear_apply]
    exact hv.symm
  constructor
  · rw [wardActualTensorWeight_eq_originalSpectra, hSlots, wardFirstLowTrilinear_apply,
      wardActualLowCut, if_pos ⟨hx'.1,hx'.2.1⟩]
    rw [hApply]
  · rw [wardActualTensorWeight_eq_originalSpectra, hSlots, wardComparableTrilinear_apply,
      wardComparableSymbol_eq, wardExtendedTriadSymbol, piecewise_eq_of_mem _ _ _ hx]
    rw [hApply]
    rfl

theorem wardActualTwoGauge_gauge_cut_tensor_eq_vertex (hx : (p,q) ∈ wardTriadDomain) :
    let r := -(p+q)
    let B := inverseMatrix G
    let H := wardActualThinSpectrum B wi wo hm hη i o z
    let Γ := (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun i => p i) (originalGaugeSpectrum z p)
      (fun i => q i) (H q) (fun i => r i) (originalGaugeSpectrum z r)
    let A := wardTwoGaugeGaugeRawTrilinear B (metricDensity G) a
    wardActualTensorWeight B ![false,true,false] (wardFirstLowTrilinear ϑ κ A) wi wo hm hη i o z (p,q) =
      (lowSlotWeight ϑ κ p q r : ℂ) * Γ := by
  classical
  intro r B H Γ A
  have hx' : p ≠ 0 ∧ q ≠ 0 ∧ r ≠ 0 := hx
  let u : Fin 3 → ComplexComponents := ![originalGaugeSpectrum z p, H q, originalGaugeSpectrum z r]
  have hSlots : (fun j : Fin 3 => if (![false,true,false] : Fin 3 → Bool) j then H (wardPhaseCovector (p,q) j)
      else originalGaugeSpectrum z (wardPhaseCovector (p,q) j)) = u := by
    funext j
    fin_cases j <;> rfl
  have hv := wardActualTwoGaugeGaugeRaw_eq_vertex G hG hg f a wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hx'.1 hx'.2.2
  have hApply : A (p,q) u = Γ := by
    rw [wardTwoGaugeGaugeRawTrilinear_apply]
    exact hv.symm
  rw [wardActualTensorWeight_eq_originalSpectra, hSlots, wardFirstLowTrilinear_apply,
    wardActualLowCut, if_pos ⟨hx'.1,hx'.2.1⟩]
  change _ * A (p,q) u = _
  rw [hApply]

end TwoGauge

theorem wardActualLowLie_tensor_eq_raw (m : Tensor2) (w : ℝ) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (p q : E) :
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    wardActualTensorWeight m ![false,true,true] (wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a))
        wi wo hm hη i o z (p,q) =
      wardActualLowCut ϑ κ (wardOneLowGaugeLieRaw m w a (originalGaugeSpectrum z p) (H q) (H (-(p+q)))) (p,q) := by
  intro H
  let u : Fin 3 → ComplexComponents := ![originalGaugeSpectrum z p, H q, H (-(p+q))]
  have hSlots : (fun j : Fin 3 => if (![false,true,true] : Fin 3 → Bool) j then H (wardPhaseCovector (p,q) j)
      else originalGaugeSpectrum z (wardPhaseCovector (p,q) j)) = u := by
    funext j
    fin_cases j <;> rfl
  rw [wardActualTensorWeight_eq_originalSpectra, hSlots, wardFirstLowTrilinear_apply]
  simp only [wardOneLowGaugeLieRawTrilinear_apply]
  rfl

end Burnett.C02
