import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLorentzTwoGauge
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThreeGauge
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowBranches
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThinTransversality
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 15800000

noncomputable section

namespace Burnett.C02

open Matrix Burnett.RicciSymbol Burnett.V06 Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (quadratic lowSlotWeight)
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum originalLowGaugePotential signedCyclicPhase)
open scoped Matrix

open private raisedWardScreenEntry from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardRaisedScreenEntry_transverse from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThinTransversality
open private wardGaugePotentialAt raisedScreenBilinear from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
open private wardActualGaugeSpectrum_eq_pureGauge from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualThreeGauge

private theorem wardInverseSymmetric (G : Mat) (f : TensorFrame.LorentzFrame (inverseMatrix G)) :
    IsSymmetricTensor (inverseMatrix G) := by
  rw [← f.inverseMetric_eq]
  exact TensorFrame.inverseMetric_symmetric f.components

private theorem wardInverseTranspose (G : Mat) (f : TensorFrame.LorentzFrame (inverseMatrix G)) :
    (inverseMatrix G)ᵀ = inverseMatrix G := by
  ext a b
  exact wardInverseSymmetric G f b a

private theorem wardPhysicalSlot (G : Mat) (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G))
    {η : ℝ} (hη : 0 < η) (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (ξ : E) :
    let B := inverseMatrix G
    let H := wardActualThinSpectrum B wi wo hm hη i o z ξ
    IsSymmetricComplexTensor H ∧ complexMetricTrace B H = 0 ∧
      (∀ j, complexContracted B (fun a => ξ a) H j = 0) ∧
      (∀ b, ∑ a, raisedWardScreenEntry B H a b * (ξ a : ℂ) = 0) := by
  intro B H
  have hB : Bᵀ = B := wardInverseTranspose G f
  have hBox := wardActualThinSpectrum_metricTransverse B wi wo hm hη i o z ξ
  have hRaise := wardRaisedScreenEntry_transverse B H ξ hB hBox.1 hBox.2
  refine ⟨wardActualThinSpectrum_symmetric B hB wi wo hm hη i o z hz ξ,
    wardActualThinSpectrum_trace_free B hB wi wo hm hη i o ε hi hio hSmall hWindow z ξ, ?_, hRaise.1⟩
  intro j
  simpa only [complexContracted, raiseCovector, Matrix.mulVec, dotProduct, H, mul_comm] using hBox.2 j

/-- Paper's high gauge raw phase coefficient is the genuine frozen cubic
vertex times the cyclic test phase on the same original three spectra. -/
theorem wardActualHighGaugeRaw_eq_vertex (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (p q : E) (hr : -(p+q) ≠ 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let H (ξ : E) := wardActualThinSpectrum B wi wo hm hη i o z ξ
    (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun i => p i) (H p)
      (fun i => q i) (H q) (fun i => r i) (originalGaugeSpectrum z r) =
      wardOneHighGaugeRaw B (metricDensity G) a (originalGaugeSpectrum z r) (H p) (H q) (p,q) := by
  intro r B H
  obtain ⟨hPs, hPt, hPc, hPr⟩ := wardPhysicalSlot G f wi wo hm hη i o ε hi hio hSmall hWindow z hz p
  obtain ⟨hQs, hQt, hQc, hQr⟩ := wardPhysicalSlot G f wi wo hm hη i o ε hi hio hSmall hWindow z hz q
  conv_lhs =>
    rw [wardActualGaugeSpectrum_eq_pureGauge z hz r hr,
      wardLorentz_highGauge_screen_components G hG hg f p q (originalLowGaugePotential z r)
        (H p) (H q) hPs hQs (wardInverseSymmetric G f) hPt hQt hPc hQc hPr hQr]
  simp only [wardOneHighGaugeRaw, mul_assoc]
  rfl

/-- With the physical frequency first, the actual two-gauge vertex
generates exactly the branch already estimated by low and comparable transfer. -/
theorem wardActualTwoGaugePhysicalRaw_eq_vertex (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (p q : E) (hq : q ≠ 0) (hr : -(p+q) ≠ 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let H := wardActualThinSpectrum B wi wo hm hη i o z p
    (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun i => p i) H
      (fun i => q i) (originalGaugeSpectrum z q) (fun i => r i) (originalGaugeSpectrum z r) =
      wardTwoGaugePhysicalLowRaw B (metricDensity G) a (originalGaugeSpectrum z q) (originalGaugeSpectrum z r) H (p,q) := by
  intro r B H
  obtain ⟨hPs, hPt, hPc, hPr⟩ := wardPhysicalSlot G f wi wo hm hη i o ε hi hio hSmall hWindow z hz p
  conv_lhs =>
    rw [wardActualGaugeSpectrum_eq_pureGauge z hz q hq, wardActualGaugeSpectrum_eq_pureGauge z hz r hr,
      wardLorentz_twoGauge_screen_components G hG hg f p q (originalLowGaugePotential z q)
        (originalLowGaugePotential z r) H hPs (wardInverseSymmetric G f) hPt hPc hPr]
  simp only [wardTwoGaugePhysicalLowRaw, mul_assoc]
  rfl

/-- With a gauge frequency first, the same true two-gauge vertex has the
physical phase in the second slot. The same signed third covector is kept. -/
theorem wardActualTwoGaugeGaugeRaw_eq_vertex (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (p q : E) (hp : p ≠ 0) (hr : -(p+q) ≠ 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let H := wardActualThinSpectrum B wi wo hm hη i o z q
    (signedCyclicPhase a p q : ℂ) * complexPrincipalVertex G (fun i => p i) (originalGaugeSpectrum z p)
      (fun i => q i) H (fun i => r i) (originalGaugeSpectrum z r) =
      wardTwoGaugeGaugeLowRaw B (metricDensity G) a (originalGaugeSpectrum z p) (originalGaugeSpectrum z r) H (p,q) := by
  intro r B H
  have hr' : -(q+p) ≠ 0 := by simpa only [add_comm q p] using hr
  have hc := wardActualTwoGaugePhysicalRaw_eq_vertex G hG hg f a wi wo hm hη i o ε hi hio hSmall hWindow z hz q p hp hr'
  have hA : signedCyclicPhase a q p = signedCyclicPhase a p q := by
    simp only [signedCyclicPhase, add_comm q p, add_comm (a q) (a p)]
  rw [hA, add_comm q p] at hc
  rw [complexPrincipalVertex_swap_first_two]
  simpa only [wardTwoGaugePhysicalLowRaw, wardTwoGaugeGaugeLowRaw, hA, add_comm q p] using hc

/-- Exact pointwise low-gauge split of the true vertex: phase difference,
transport physical phases, and the two physical Lie-index phases. -/
theorem wardActualLowGauge_cut_eq_vertex (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a) (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) :
    let r := -(p+q)
    let B := inverseMatrix G
    let w := metricDensity G
    let H (ξ : E) := wardActualThinSpectrum B wi wo hm hη i o z ξ
    let L := (lowSlotWeight ϑ κ p q r : ℂ)
    let α := (signedCyclicPhase a p q : ℂ)
    let Γ := complexPrincipalVertex G (fun i => p i) (originalGaugeSpectrum z p)
      (fun i => q i) (H q) (fun i => r i) (H r)
    L * α * Γ =
      L * α * (-(w : ℂ) * ((quadratic B r : ℂ) - (quadratic B q : ℂ)) *
        raisedWardGaugeDot B (originalLowGaugePotential z p) (q-r) * frozenWardScreenPair B (H q) (H r)) +
      wardLowGaugeMiddleSymbol ϑ κ B w a (originalGaugeSpectrum z p) (H q) (H r) (p,q) +
      wardActualLowCut ϑ κ (wardOneLowGaugeLieRaw B w a (originalGaugeSpectrum z p) (H q) (H r)) (p,q) := by
  intro r B w H L α Γ
  obtain ⟨hQs, hQt, hQc, _⟩ := wardPhysicalSlot G f wi wo hm hη i o ε hi hio hSmall hWindow z hz q
  obtain ⟨hRs, hRt, hRc, _⟩ := wardPhysicalSlot G f wi wo hm hη i o ε hi hio hSmall hWindow z hz r
  dsimp only [Γ]
  conv_lhs =>
    rw [wardActualGaugeSpectrum_eq_pureGauge z hz p hp,
      wardLorentz_oneGauge_screen_components G hG hg f p q (originalLowGaugePotential z p) (H q) (H r)
        hQs hRs (wardInverseSymmetric G f) hQt hRt hQc hRc]
  rw [wardLowGaugeMiddleSymbol, if_pos ⟨hp,hq⟩, wardActualLowCut, if_pos ⟨hp,hq⟩]
  simp only [wardOneLowGaugeLieRaw]
  let v := originalLowGaugePotential z p
  let C := frozenWardScreenPair B (H q) (H r)
  let s := (quadratic B q : ℂ)
  let t := (quadratic B r : ℂ)
  let U := wardScreenLieContraction B (H q) (H r) v p
  let V := wardScreenLieContraction B (H r) (H q) v p
  let D := -(w : ℂ) * (t - s) * raisedWardGaugeDot B v (q-r) * C
  change L * α * (D + (w : ℂ) * raisedWardGaugeDot B v p * (s + t) * C -
      2 * (w : ℂ) * s * U - 2 * (w : ℂ) * t * V) =
    L * α * D + L * (α * (w : ℂ) * raisedWardGaugeDot B v p * (s + t) * C) +
      L * ((-2 : ℂ) * α * (w : ℂ) * (s * U + t * V))
  ring

end Burnett.C02
