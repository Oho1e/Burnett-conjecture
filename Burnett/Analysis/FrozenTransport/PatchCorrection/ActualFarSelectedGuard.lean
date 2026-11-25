import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarFrequencyEnergy

set_option autoImplicit false
set_option maxHeartbeats 5800000
set_option maxRecDepth 5200

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02 Burnett.C03 Burnett.V03
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint tau radianFourier)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open Burnett.V11 (GaugeProfileBound)
open scoped ContDiff ENNReal BigOperators ComplexConjugate Matrix.Norms.Elementwise
open private actualThinFar_zero_low from Burnett.Analysis.FrozenTransport.ActualFarHighAdjoint
open private waveQuadratic_eq_quadratic from Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarFrequencyEnergy

def ActualFarPhaseIdentities (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ) : Prop :=
  ∀ (k j l : OrderedPair) (p q r : Vec), p ≠ 0 → q ≠ 0 → r ≠ 0 → p + q + r = 0 →
    let B := (‖q‖ : ℂ) * actualThinFarCubicCorrection g a ϑ κ δ b i o hm hη inn out k j l
      (physicalFarProfilePoint p q)
    let N := actualThinFarWeightedNumerator g a ϑ κ δ i o hm hη inn out k j l p q r
    let phase := Complex.I * (signedQuadraticPhase (inverseMatrix g) p q : ℂ)
    B = N / phase ∧ phase * B = N

/-- The selected quotient determines the adjoint with the same guard. -/
theorem actualFarRadianKernel_highAdjoint_of_phase (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (phase : ActualFarPhaseIdentities g a ϑ κ δ b i o hm hη inn out)
    (odd : ∀ x : Vec, x ≠ 0 → a (-x) = -a x) (k j l : OrderedPair) (p q : Vec) :
    conj (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k l j (-p, p + q)) =
      actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l (p, q) := by
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
  have swapSum : -p + (p + q) + -q = 0 := by rw [hswapQ, add_neg_cancel]
  have eq := (phase k j l p q (-(p + q)) hp hq hr' (add_neg_cancel (p + q))).1
  have eq' := (phase k l j (-p) (p + q) (-q) (neg_ne_zero.mpr hp) hr (neg_ne_zero.mpr hq) swapSum).1
  have hnum := actualThinFarWeightedNumerator_highAdjoint g a odd ϑ κ δ i o hm hη inn out k j l hp hq hr'
  simp only [neg_neg] at hnum
  simp only [actualFarRadianKernel, hswapQ, eq', eq, map_mul, map_div₀, Complex.conj_ofReal, hnum,
    Complex.conj_I, signedQuadraticPhase_highAdjoint, Complex.ofReal_neg, map_neg, neg_mul_neg]
  ring

/-- The original Fourier integral is identified using the selected guard. -/
theorem originalFarPatch_fourierEnergy_of_phase (g : Mat) (a : Vec → ℝ) (ha : ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (cut : ∀ s : ℝ, 1 ≤ s → ϑ s = 0)
    (κ : ℝ) (hκ : 0 < κ) (hs : κ < 1 / 16) (δ b i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (phase : ActualFarPhaseIdentities g a ϑ κ δ b i o hm hη inn out) (M : ℝ) (hM : 0 ≤ M)
    (bound : ∀ k J I, ∀ y ∈ (Metric.closedBall (0 : E) (1 / 4) ×ˢ Metric.sphere (0 : E) 1) ×ˢ Metric.sphere (0 : E) 1,
      ‖actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I y‖ ≤ M) (z : ProjectionSchwartzMatrix) :
    let N := originalFarPatchFourierWeight g a ϑ κ δ i o hm hη inn out z
    Integrable N ∧ (tau ^ 8)⁻¹ • ∫ x, N x = actualFarPatchEnergy g a ϑ κ δ b i o hm hη inn out z := by
  classical
  intro N
  let m := inverseMatrix g
  let f := projectionFullSchwartz z
  let W (I J k : OrderedPair) := originalFarEntryFourierWeight g a ϑ κ δ i o hm hη inn out k J I z
  let Q (I J k : OrderedPair) := actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I
  let T (I J k : OrderedPair) := Complex.I *
    (radianHighPair (Q I J k) (f k.1 k.2) (f J.1 J.2) (constantWave m (f I.1 I.2)) -
      radianHighPair (Q I J k) (f k.1 k.2) (constantWave m (f J.1 J.2)) (f I.1 I.2))
  have atzero (k : OrderedPair) : radianFourier (projectionFullSchwartz z k.1 k.2) 0 = 0 := by
    have hzero : gaugeProjectionInfrared 0 = 0 := gaugeProjectionInfrared_zero (by norm_num)
    simp [projectionFullSchwartz_radianFourier, regularizedComplexGaugeProjection, hzero]
  have one (I J k : OrderedPair) : Integrable (W I J k) ∧ (tau ^ 8)⁻¹ • ∫ x, W I J k x = T I J k := by
    obtain ⟨meas, order⟩ := actualFarKernel_measurable_orderOne g a ha ϑ hϑ cut κ hκ hs δ b i o hm hη inn out
      k J I M hM (bound k J I)
    let w₁ := radianHighPairWeight (Q I J k) (f k.1 k.2) (f J.1 J.2) (constantWave m (f I.1 I.2))
    let w₂ := radianHighPairWeight (Q I J k) (f k.1 k.2) (constantWave m (f J.1 J.2)) (f I.1 I.2)
    have h₁ : Integrable w₁ := integrable_radianHighPairWeight_of_orderOne _ meas M hM order _ _ _
    have h₂ : Integrable w₂ := integrable_radianHighPairWeight_of_orderOne _ meas M hM order _ _ _
    have pair : W I J k = fun x => Complex.I * (w₁ x - w₂ x) := by
      funext x
      obtain ⟨p,q⟩ := x
      simp only [W, originalFarEntryFourierWeight, w₁, w₂, radianHighPairWeight, radianFourier_constantWave,
        map_mul, Complex.conj_ofReal]
      by_cases hp : p = 0
      · subst p
        simp [atzero, f]
      by_cases hq : q = 0
      · subst q
        simp [atzero, f]
      by_cases hr : p + q = 0
      · have hr' : q + p = 0 := by rwa [add_comm]
        simp [hr', atzero, f]
      have eq := (phase k J I p q (-(p + q)) hp hq (neg_ne_zero.mpr hr) (add_neg_cancel (p + q))).2
      rw [← eq]
      simp only [Q, actualFarRadianKernel, waveQuadratic_eq_quadratic, signedQuadraticPhase, Complex.ofReal_sub]
      ring
    refine ⟨pair.symm ▸ (h₁.sub h₂).const_mul _, ?_⟩
    rw [pair, integral_const_mul, integral_sub h₁ h₂]
    simp only [T, radianHighPair, w₁, w₂, Complex.real_smul]
    ring
  have byI (I : OrderedPair) : Integrable (fun x => ∑ J : OrderedPair, ∑ k : OrderedPair, W I J k x) :=
    integrable_finset_sum _ fun J _ => integrable_finset_sum _ fun k _ => (one I J k).1
  refine ⟨integrable_finset_sum _ (fun I _ => byI I), ?_⟩
  change (tau ^ 8)⁻¹ • (∫ x, ∑ I : OrderedPair, ∑ J : OrderedPair, ∑ k : OrderedPair, W I J k x) = ∑ I, ∑ J, ∑ k, T I J k
  rw [integral_finset_sum _ (fun I _ => byI I), Finset.smul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  rw [integral_finset_sum _ (fun J _ => integrable_finset_sum _ fun k _ => (one I J k).1), Finset.smul_sum]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [integral_finset_sum _ (fun k _ => (one I J k).1), Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => (one I J k).2

/-- Select the compact phase guard once, before the opening angle, center,
ordered slots, and actual C03 patch fields. The same guarded kernel gives the
literal Fourier numerator and the high-slot adjoint. The C03 estimate then
bounds that very integral with the original inverse-coefficient and source data. -/
theorem exists_originalFarPatch_selectGuard :
    ∃ (N : ℕ) (Co Cw : ℝ), 0 ≤ Co ∧ 0 ≤ Cw ∧
      ∀ {K : Set Form}, IsCompact K → (∀ m ∈ K, Nonempty (LorentzFrame m)) → ∀ D : ℝ, 0 ≤ D →
      ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ (g : Mat), inverseMatrix g ∈ K →
      ∀ (a : Vec → ℝ), (∀ x : Vec, x ≠ 0 → a (-x) = -a x) →
        (∀ d : ℝ, 0 < d → ∀ x : Vec, x ≠ 0 → a (d • x) = d * a x) → ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec) →
      ∀ (ϑ : ℝ → ℝ), ContDiff ℝ ∞ ϑ → (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) →
      ∀ κ : ℝ, 0 < κ → κ < 1 / 16 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)),
      ∀ (inn out : ℝ), 0 ≤ inn → inn < out → out ≤ D → ∀ hη : 0 < c * κ * δ ^ 2,
        ActualFarPhaseIdentities g a ϑ κ δ b i o hm hη inn out ∧
        (∀ (k j l : OrderedPair) (p q : Vec),
          conj (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k l j (-p, p + q)) =
            actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k j l (p, q)) ∧
        ∀ M : ℝ, 0 ≤ M → (∀ k J I, GaugeProfileBound N M
          (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I)) →
        ∀ (d : Fin 4 → Fin 4 → SchwartzMap E ℝ) (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix)
          (W : Set E) (B ℓ e : ℝ), 1 ≤ B → 0 < ℓ → 0 ≤ e → Co * M ≤ B → 2 * Cw * M ≤ B →
        (∀ r s, d r s = d s r) → (∀ r s x, A.entry r s x = ((inverseMatrix g r s + d r s x : ℝ) : ℂ)) →
        (∀ r s x, |d r s x| ≤ B * (ℓ + e)) → (∀ r s x, ‖fderiv ℝ (d r s : E → ℝ) x‖ ≤ B * (1 + e / ℓ)) →
        (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
          B * (volume W ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e)) →
        (∃ v, ProjectedPatchLpBounds 2 z W v ((B / 4) * (1 + e / ℓ))) →
        ProjectedPatchLpBounds 4 z W (B * e) ((B / 4) * (1 + e / ℓ)) →
        let weight := originalFarPatchFourierWeight g a ϑ κ δ i o hm hη inn out z
        let integral := (tau ^ 8)⁻¹ • ∫ x, weight x
        Integrable weight ∧ integral = actualFarPatchEnergy g a ϑ κ δ b i o hm hη inn out z ∧
        ‖integral‖ ≤ (16 ^ 3 : ℝ) * (3 * B ^ 5) * (volume W).toReal * Burnett.C04.correctionEnvelope ℓ e := by
  obtain ⟨N, Co, Cw, hCo, hCw, estimate⟩ := exists_actualFar_projectedPatch_envelope
  refine ⟨N, Co, Cw, hCo, hCw, ?_⟩
  intro K hK hFrame D hD
  obtain ⟨c₀, b, hc₀, hb, exactness⟩ := exists_actualThinFar_exact_physicalQuotient hK hFrame D hD
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro g hg a odd hom ha ϑ hϑ cut flat κ hκ hs δ hδ hd c hc hc' i o hm inn out hin hio hout hη
  have phase : ActualFarPhaseIdentities g a ϑ κ δ b i o hm hη inn out :=
    fun k j l p q r hp hq hr hsum => exactness g hg a odd hom (ha.of_le (by simp)) ϑ cut flat κ hκ hs δ hδ hd c hc hc'
      i o hm inn out hin hio hout k j l p q r hp hq hr hsum hη
  refine ⟨phase, actualFarRadianKernel_highAdjoint_of_phase g a ϑ κ δ b i o hm hη inn out phase odd, ?_⟩
  intro M hM jets d A z W B ℓ e hB hℓ he ho hw hd' hA hD' hL hSrc h₂ h₄ weight integral
  have zeroth (k J I : OrderedPair) (y : Joint × E) (hy : y ∈ Burnett.V11.gaugeAngularWindow) :
      ‖actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I y‖ ≤ M := by
    obtain ⟨_, _, _, _, hj⟩ := jets k J I
    simpa only [norm_iteratedFDeriv_zero] using hj 0 (Nat.zero_le N) y hy
  obtain ⟨int, eq⟩ := originalFarPatch_fourierEnergy_of_phase g a ha ϑ hϑ cut κ hκ hs δ b i o hm hη inn out
    phase M hM zeroth z
  refine ⟨int, eq, ?_⟩
  change ‖(tau ^ 8)⁻¹ • ∫ x, originalFarPatchFourierWeight g a ϑ κ δ i o hm hη inn out z x‖ ≤ _
  rw [eq]
  exact estimate g a ϑ cut κ hκ hs δ b i o hm hη inn out M hM jets d A z W B ℓ e hB hℓ he ho hw hd' hA hD' hL hSrc h₂ h₄

end Burnett.V10.OriginalGaugeCompatibility
