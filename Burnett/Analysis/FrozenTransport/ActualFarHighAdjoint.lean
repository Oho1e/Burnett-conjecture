import Burnett.Analysis.FrozenTransport.ActualFarPhysicalQuotient

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option maxRecDepth 3800

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Burnett.P01 Burnett.C02 Burnett.V03 Burnett.V06
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff ComplexConjugate Matrix.Norms.Elementwise
open private orderedBasis from Burnett.Analysis.TransportPatches.ActualWideOrderedSymbols

private theorem actualThin_column_conj (m : Form) (i o : ℝ) (hm : WideScreenFrequencySmooth i o m)
    {η : ℝ} (hη : 0 < η) (inn out : ℝ) (v : Vec) (k j : OrderedPair) :
    (thinScreenAngular m i o hm hη inn out).complex (-v) k j =
      conj ((thinScreenAngular m i o hm hη inn out).complex v k j) := by
  have hthin : thinConeProfile m η inn out (-v) = thinConeProfile m η inn out v := by
    rw [← neg_one_smul ℝ v]
    exact thinConeProfile_degreeZero m η inn out (-1) (by norm_num) v
  have hwide : (wideScreenAngular i o m hm).matrix (-v) k j = (wideScreenAngular i o m hm).matrix v k j := by
    exact congrFun (congrFun (globalAngularScreenSymbol_even i o m (orderedBasis j) (fun s => v s)) k.1) k.2
  simp only [RealOrderedAngularMatrix.complex, thinScreenAngular, Matrix.smul_apply, hthin, hwide,
    Complex.conj_ofReal]

theorem actualThinFarWeightedNumerator_highAdjoint (g : Mat) (a : Vec → ℝ)
    (odd : ∀ v : Vec, v ≠ 0 → a (-v) = -a v) (ϑ : ℝ → ℝ) (κ δ i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) {p q r : Vec} (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    conj (actualThinFarWeightedNumerator g a ϑ κ δ i o hm hη inn out k l j (-p) (-r) (-q)) =
      actualThinFarWeightedNumerator g a ϑ κ δ i o hm hη inn out k j l p q r := by
  have mask : lowSlotWeight ϑ κ (-p) (-r) (-q) = lowSlotWeight ϑ κ p q r := by
    simp [lowSlotWeight, add_comm]
  have angles : angularNearWeight ϑ δ (-p) (-r) (-q) = angularNearWeight ϑ δ p q r := by
    simp [angularNearWeight, projectiveWedgeSq_neg_left, projectiveWedgeSq_neg_right, mul_comm]
  simp only [actualThinFarWeightedNumerator, mask, angles, map_mul, Complex.conj_ofReal, actualThin_column_conj]
  rw [physicalCubicNumerator_highAdjoint orderedMetricDirection g a odd hp hq hr]

def actualFarRadianKernel (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) (x : Joint) : ℂ :=
  (gaugeProjectionInfrared (2 * ‖x.2‖) : ℂ) * (gaugeProjectionInfrared (2 * ‖x.1 + x.2‖) : ℂ) *
    ((‖x.2‖ : ℂ) * actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l
      (physicalFarProfilePoint x.1 x.2))

private theorem actualThinFar_zero_low (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k j l : OrderedPair) (q : Vec) :
    actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l (physicalFarProfilePoint 0 q) = 0 := by
  have hphase : normalizedFarPhase (inverseMatrix g) (physicalFarProfilePoint 0 q) = 0 := by
    simp [physicalFarProfilePoint, unitRep, normalizedFarPhase, pairing, rowValue]
  simp [actualThinFarCubicCorrection, farPhysicalCubicCorrection, cutoffGuardedFarProfile,
    guardedFarCorrectionProfile, hphase, guardedFarReciprocal]

/-- Both exact high windows and the guarded physical quotient preserve the
adjunction of the true high slots. The constants are chosen on the original
compact family of frozen inverse metrics. -/
theorem exists_actualFarRadianKernel_highAdjoint {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (LorentzFrame m)) (D : ℝ) (hD : 0 ≤ D) :
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ (g : Mat), inverseMatrix g ∈ K →
      ∀ (a : Vec → ℝ), (∀ x : Vec, x ≠ 0 → a (-x) = -a x) →
        (∀ d : ℝ, 0 < d → ∀ x : Vec, x ≠ 0 → a (d • x) = d * a x) →
        ContDiffOn ℝ 1 a ({0}ᶜ : Set Vec) →
      ∀ (ϑ : ℝ → ℝ), (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) →
      ∀ κ : ℝ, 0 < κ → κ < 1 / 16 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)),
      ∀ (inn out : ℝ), 0 ≤ inn → inn < out → out ≤ D →
      ∀ (k j l : OrderedPair) (p q : Vec), ∀ hη : 0 < c * κ * δ ^ 2,
        conj (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k l j (-p, p + q)) =
          actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l (p, q) := by
  obtain ⟨c₀, b, hc₀, hb, exactness⟩ := exists_actualThinFar_exact_physicalQuotient hK hFrame D hD
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro g hg a odd hom ha ϑ cut flat κ hκ hs δ hδ hd c hc hc' i o hm inn out hin hio hout k j l p q hη
  have hzero : gaugeProjectionInfrared 0 = 0 := gaugeProjectionInfrared_zero (by norm_num)
  have hswapQ : -p + (p + q) = q := by abel
  by_cases hp : p = 0
  · subst p
    simp only [neg_zero, zero_add, actualFarRadianKernel, actualThinFar_zero_low, mul_zero, map_zero]
  by_cases hq : q = 0
  · subst q
    simp [actualFarRadianKernel, hzero]
  by_cases hr : p + q = 0
  · simp only [actualFarRadianKernel, hr, norm_zero, mul_zero, hzero, Complex.ofReal_zero,
      zero_mul, map_zero]
  have hr' : -(p + q) ≠ 0 := neg_ne_zero.mpr hr
  have sum := add_neg_cancel (p + q)
  have swapSum : -p + (p + q) + -q = 0 := by rw [hswapQ, add_neg_cancel]
  have phys := exactness g hg a odd hom ha ϑ cut flat κ hκ hs δ hδ hd c hc hc' i o hm inn out hin hio hout
  have eq := (phys k j l p q (-(p + q)) hp hq hr' sum hη).1
  have eq' := (phys k l j (-p) (p + q) (-q) (neg_ne_zero.mpr hp) hr (neg_ne_zero.mpr hq) swapSum hη).1
  have hnum := actualThinFarWeightedNumerator_highAdjoint g a odd ϑ κ δ i o hm hη inn out k j l hp hq hr'
  simp only [neg_neg] at hnum
  simp only [actualFarRadianKernel, hswapQ, eq', eq, map_mul, map_div₀, Complex.conj_ofReal, hnum,
    Complex.conj_I, signedQuadraticPhase_highAdjoint, Complex.ofReal_neg, map_neg, neg_mul_neg]
  ring

end Burnett.V10.OriginalGaugeCompatibility
