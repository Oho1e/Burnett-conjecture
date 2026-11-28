import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeCorrectionBridge
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTensorVertexLink
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCubicBranchAssembly
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeTensorForm

set_option autoImplicit false
set_option maxRecDepth 7600
set_option maxHeartbeats 18600000

noncomputable section

namespace Burnett.C02

open Matrix MeasureTheory Burnett.RicciSymbol Burnett.V06 Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.Analysis.ProjectiveNullCaps (quadratic lowSlotWeight comparableSlotWeight)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz gaugeProjectionInfrared)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V08 (originalGaugeSpectrum originalLowGaugePotential lowGaugeTransportCoefficient signedCyclicPhase)
open scoped Matrix ComplexConjugate

open private wardQuarterTraceReversal from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugeCorrectionBridge

/-- The exact ordered numerator in the original low-gauge correction
commutator, including the original nested infrared windows. -/
def wardOrderedGaugeCorrectionNumerator (ϑ : ℝ → ℝ) (κ : ℝ) (G : Mat) (a : E → ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (x : Joint) : ℂ :=
  let p := x.1
  let q := x.2
  let m := inverseMatrix G
  let S := (thinScreenAngular m wi wo hm hη i o).matrix
  let L := lowSlotWeight ϑ κ p q (-(p+q))
  ∑ I : OrderedPair, ∑ J : OrderedPair,
    ((L * gaugeProjectionInfrared (2 * ‖q‖) * gaugeProjectionInfrared (2 * ‖p+q‖) : ℝ) : ℂ) *
    lowGaugeTransportCoefficient m (metricDensity G) a (originalLowGaugePotential z) (wardQuarterTraceReversal m) S p q I J *
    radianFourier (projectionFullSchwartz z J.1 J.2) q *
    conj (radianFourier (projectionFullSchwartz z I.1 I.2) (q+p))

/-- On the first-low gauge sector, the exact original cyclic energy
integrand is the original correction numerator plus the two bounded
physical-phase integrands, with exactly the cyclic factor on the latter. -/
theorem wardCyclicActualLowGaugeWeight_eq_original (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) :
    let m := inverseMatrix G
    let w := metricDensity G
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let A := wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a)
    wardCyclicCubicBranchWeight ϑ κ 0 G a (originalGaugeSpectrum z) H H (p,q) =
      wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z (p,q) +
      (-Complex.I / 3) * (wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z (p,q) +
        wardActualTensorWeight m ![false,true,true] A wi wo hm hη i o z (p,q)) := by
  intro m w H A
  have hmSym : (inverseMatrix G)ᵀ = inverseMatrix G := by
    have ht : IsSymmetricTensor (inverseMatrix G) := by
      rw [← f.inverseMetric_eq]
      exact TensorFrame.inverseMetric_symmetric f.components
    ext a b
    exact ht b a
  have hTrace := wardActualThinSpectrum_trace_free m hmSym wi wo hm hη i o ε hi hio hSmall hWindow z q
  have hCorr := wardActualLowGaugeTransport_eq_orderedNumerator G a ϑ κ wi wo hm hη i o z hReal p q hTrace
  have hWard := wardActualLowGauge_cut_eq_vertex G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall hWindow z hz p q hp hq
  let r := -(p+q)
  let L := (lowSlotWeight ϑ κ p q r : ℂ)
  let α := (signedCyclicPhase a p q : ℂ)
  let Γ := complexPrincipalVertex G (fun i => p i) (originalGaugeSpectrum z p) (fun i => q i) (H q) (fun i => r i) (H r)
  let D := -(w : ℂ) * ((quadratic m r : ℂ) - (quadratic m q : ℂ)) *
    raisedWardGaugeDot m (originalLowGaugePotential z p) (q-r) * frozenWardScreenPair m (H q) (H r)
  let M := wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z (p,q)
  let N := wardActualTensorWeight m ![false,true,true] A wi wo hm hη i o z (p,q)
  have hN : N = wardActualLowCut ϑ κ (wardOneLowGaugeLieRaw m w a (originalGaugeSpectrum z p) (H q) (H r)) (p,q) :=
    wardActualLowLie_tensor_eq_raw m w a ϑ κ wi wo hm hη i o z p q
  have hwEq : L * α * Γ = L * α * D + M + N := by
    rw [hN]
    exact hWard
  have hcEq : (-Complex.I / 3) * (L * α * D) = wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z (p,q) :=
    hCorr
  change L * ((-Complex.I / 3) * α * Γ) = _ + (-Complex.I / 3) * (M + N)
  calc
    _ = (-Complex.I / 3) * (L * α * Γ) := by ring
    _ = _ := by rw [hwEq, ← hcEq]; ring


private theorem wardAE_first_two_nonzero :
    ∀ᵐ x ∂(volume : Measure Joint), x.1 ≠ (0 : E) ∧ x.2 ≠ (0 : E) := by
  have hFrequency : ∀ᵐ ξ ∂(volume : Measure E), ξ ≠ (0 : E) := by simp [ae_iff]
  rw [Measure.volume_eq_prod E E]
  have hp : MeasurableSet {x : Joint | x.1 ≠ 0} :=
    (isOpen_ne_fun continuous_fst continuous_const).measurableSet
  have hq : MeasurableSet {x : Joint | x.2 ≠ 0} :=
    (isOpen_ne_fun continuous_snd continuous_const).measurableSet
  have hF : ∀ᵐ x ∂(volume : Measure E).prod volume, (x : Joint).1 ≠ 0 := (Measure.ae_prod_iff_ae_ae hp).2
    (hFrequency.mono fun ξ hξ => Filter.Eventually.of_forall fun _ : E => hξ)
  have hS : ∀ᵐ x ∂(volume : Measure E).prod volume, (x : Joint).2 ≠ 0 := (Measure.ae_prod_iff_ae_ae hq).2
    (Filter.Eventually.of_forall fun _ : E => hFrequency)
  exact hF.and hS

/-- The actual first-low one-gauge energy is absolutely integrable once
the actual correction and phase numerators are, with the exact cyclic
factor and the same radian integral normalization. -/
theorem wardCyclicActualLowGaugeForm_eq_original (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) :
    let m := inverseMatrix G
    let w := metricDensity G
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let A := wardFirstLowTrilinear ϑ κ (wardOneLowGaugeLieRawTrilinear m w a)
    let N := wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z
    let M := wardLowGaugeMiddleTensorWeight ϑ κ m w a wi wo hm hη i o z
    let B := wardActualTensorWeight m ![false,true,true] A wi wo hm hη i o z
    Integrable N → Integrable M → Integrable B →
    Integrable (wardCyclicCubicBranchWeight ϑ κ 0 G a (originalGaugeSpectrum z) H H) ∧
    wardCyclicCubicBranchForm ϑ κ 0 G a (originalGaugeSpectrum z) H H =
      ((tau ^ 8)⁻¹ • ∫ x, N x) + (-Complex.I / 3) *
        (wardLowGaugeMiddleTensorForm ϑ κ m w a wi wo hm hη i o z +
          wardActualTensorForm m ![false,true,true] A wi wo hm hη i o z) := by
  intro m w H A N M B hN hM hB
  let k := -Complex.I / 3
  let S (x : Joint) := N x + k * (M x + B x)
  have hAE : wardCyclicCubicBranchWeight ϑ κ 0 G a (originalGaugeSpectrum z) H H =ᵐ[volume] S := by
    filter_upwards [wardAE_first_two_nonzero] with x hx
    obtain ⟨p,q⟩ := x
    exact wardCyclicActualLowGaugeWeight_eq_original G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall
      hWindow z hz hReal p q hx.1 hx.2
  have hMI : Integrable (fun x => M x + B x) := hM.add hB
  have hSI : Integrable S := hN.add (hMI.const_mul k)
  refine ⟨hSI.congr hAE.symm,?_⟩
  unfold wardCyclicCubicBranchForm
  rw [integral_congr_ae hAE]
  change (tau^8)⁻¹ • (∫ x, N x + k * (M x + B x)) =
    ((tau^8)⁻¹ • ∫ x, N x) + k * (((tau^8)⁻¹ • ∫ x, M x) + ((tau^8)⁻¹ • ∫ x, B x))
  rw [integral_add hN (hMI.const_mul k), integral_const_mul, integral_add hM hB]
  simp only [smul_add, Complex.real_smul]
  ring

end Burnett.C02
