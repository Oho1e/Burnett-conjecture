import Burnett.Analysis.FrozenTransport.ActualFarHighAdjoint
import Burnett.Analysis.CubicEnergy.AngularHarmonics.OriginalAngularExpansion
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotAdjoint

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option maxRecDepth 4000

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Metric MeasureTheory Burnett.A06 Burnett.A07 Burnett.P01 Burnett.C02 Burnett.V03
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff ComplexConjugate Matrix.Norms.Elementwise
open private physical_low from Burnett.Analysis.FrozenTransport.ActualV10Infrared

def correctionInputWindow (s : ℝ) : ℝ := gaugeProjectionInfrared (2 * s)

def correctionRatioWindow (s : ℝ) : ℝ := 1 - gaugeProjectionInfrared (64 * s)

/-- The unexpanded A08 entry is exactly the physical far kernel with its high
input window. The original output window is displayed separately. -/
theorem actualFarRadianKernel_eq_output_filtered_A08 (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ)
    (cut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0) (κ : ℝ) (hκ : 0 < κ) (hs : κ < 1 / 16) (δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) (p q : Vec) :
    actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l (p, q) =
      (correctionInputWindow ‖p + q‖ : ℂ) *
      originalRegularizedAngularSymbol correctionInputWindow correctionRatioWindow
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l) (p, q) := by
  let x := physicalFarProfilePoint p q
  let B := (‖q‖ : ℂ) * actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l x
  let hi := (correctionInputWindow ‖q‖ : ℂ)
  let ho := (correctionInputWindow ‖p + q‖ : ℂ)
  let ρ := (correctionRatioWindow (‖‖q‖⁻¹ • p‖ ^ 2) : ℂ)
  have inert : ρ * B = B :=
    actualThinFar_ratio_guard_inert g a ϑ cut κ hκ hs δ b i o hm hη inn out k j l p q
  have unfoldSymbol : originalRegularizedAngularSymbol correctionInputWindow correctionRatioWindow
      (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l) (p, q) = hi * (ρ * B) := by
    simp only [originalRegularizedAngularSymbol, regularizedLowCartesianSymbol, lowCartesianSymbol,
      normalizedHighPair, roundSphereRadialNormalize, actualFarAngularProfile,
      physicalFarProfilePoint, unitRep, hi, ρ, B, x, Complex.real_smul]
    ring
  change hi * ho * B = _
  rw [unfoldSymbol, inert]
  ring

/-- For any true low Schwartz component or its coordinate derivative, the
actual far pairing is precisely the A08 pairing for arbitrary high slots. -/
theorem actualFarA08_pair (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ)
    (cut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0) (κ : ℝ) (hκ : 0 < κ) (hs : κ < 1 / 16) (δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) (H : E → ℂ) (hH : ∀ p, ‖p‖ ≤ 1 → radianFourier H p = 0)
    (u v : E → ℂ) :
    radianHighPair (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l) H u v =
      radianHighPair (originalRegularizedAngularSymbol correctionInputWindow correctionRatioWindow
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l)) H u v := by
  unfold radianHighPair
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  obtain ⟨p,q⟩ := x
  rw [radianHighPairWeight, radianHighPairWeight, actualFarRadianKernel_eq_output_filtered_A08
    g a ϑ cut κ hκ hs δ b i o hm hη inn out k j l p q]
  by_cases hp : ‖p‖ ≤ 1
  · simp [hH p hp]
  by_cases hq : q = 0
  · subst q
    simp [originalRegularizedAngularSymbol, regularizedLowCartesianSymbol, lowCartesianSymbol]
  by_cases hlow : lowSlotWeight ϑ κ p q (-(p + q)) = 0
  · have hz : ϑ (farLowArgument κ (physicalFarProfilePoint p q)) = 0 := by
      rw [physical_low hq hκ]
      exact hlow
    have hprofile : actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l
        (physicalFarProfilePoint p q) = 0 := by
      simp only [actualThinFarCubicCorrection, farPhysicalCubicCorrection, cutoffGuardedFarProfile,
        farCutoffExtension, hz, zero_mul, Complex.ofReal_zero]
    have hsymbol : originalRegularizedAngularSymbol correctionInputWindow correctionRatioWindow
        (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k j l) (p, q) = 0 := by
      change _ • (_ • (_ • actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l
        (physicalFarProfilePoint p q))) = (0 : ℂ)
      simp only [hprofile, smul_zero]
    simp only [hsymbol, mul_zero, zero_mul]
  have hsmall := lowSlotWeight_nonzero_small cut hκ hs (add_neg_cancel (p + q)) hq hlow
  have hstrict := mul_lt_mul_of_pos_right hs (norm_pos_iff.mpr hq)
  have htri : ‖q‖ ≤ ‖p+q‖+‖p‖ := by
    simpa only [add_sub_cancel_left] using norm_sub_le (p+q) p
  have ho : correctionInputWindow ‖p + q‖ = 1 := gaugeProjectionInfrared_one (by linarith)
  simp only [ho, Complex.ofReal_one, one_mul]

end Burnett.V10.OriginalGaugeCompatibility
