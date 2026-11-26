import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarKernelOrder
import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarPatchEnvelope

set_option autoImplicit false
set_option maxHeartbeats 5800000
set_option maxRecDepth 5200

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02 Burnett.V03
open Burnett.Analysis.ProjectiveNullCaps Burnett.Analysis.TransportWardSymbol
open Burnett.A02.FrequencySplit (E Joint tau radianFourier)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.RicciSymbol.TensorFrame (LorentzFrame)
open scoped ContDiff BigOperators ComplexConjugate Matrix.Norms.Elementwise

private theorem waveQuadratic_eq_quadratic (m : Form) (p : Vec) : waveQuadratic m p = quadratic m p := by
  simp only [waveQuadratic, quadratic, pairing, rowValue, Finset.sum_mul]
  exact Finset.sum_comm

def originalFarEntryFourierWeight (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (k J I : OrderedPair) (z : ProjectionSchwartzMatrix) (x : Joint) : ℂ :=
  let f := projectionFullSchwartz z
  (gaugeProjectionInfrared (2 * ‖x.2‖) : ℂ) * (gaugeProjectionInfrared (2 * ‖x.1 + x.2‖) : ℂ) *
    actualThinFarWeightedNumerator g a ϑ κ δ i o hm hη inn out k J I x.1 x.2 (-(x.1 + x.2)) *
    radianFourier (f k.1 k.2) x.1 * radianFourier (f J.1 J.2) x.2 *
    conj (radianFourier (f I.1 I.2) (x.2 + x.1))

def originalFarPatchFourierWeight (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ) (κ δ i o : ℝ)
    (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ)
    (z : ProjectionSchwartzMatrix) (x : Joint) : ℂ :=
  ∑ I : OrderedPair, ∑ J : OrderedPair, ∑ k : OrderedPair,
    originalFarEntryFourierWeight g a ϑ κ δ i o hm hη inn out k J I z x

/-- Removing the guarded denominator via the true constant wave polynomial
recovers the original full far numerator and its original three Fourier fields. -/
theorem exists_originalFarPatch_fourierEnergy {K : Set Form} (hK : IsCompact K)
    (hFrame : ∀ m ∈ K, Nonempty (LorentzFrame m)) (D : ℝ) (hD : 0 ≤ D) :
    ∃ c₀ b : ℝ, 0 < c₀ ∧ 0 < b ∧
      ∀ (g : Mat), inverseMatrix g ∈ K →
      ∀ (a : Vec → ℝ), (∀ x : Vec, x ≠ 0 → a (-x) = -a x) →
        (∀ d : ℝ, 0 < d → ∀ x : Vec, x ≠ 0 → a (d • x) = d * a x) → ContDiffOn ℝ ∞ a ({0}ᶜ : Set Vec) →
      ∀ (ϑ : ℝ → ℝ), ContDiff ℝ ∞ ϑ → (∀ t : ℝ, 1 ≤ t → ϑ t = 0) →
        (∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) →
      ∀ κ : ℝ, 0 < κ → κ < 1 / 16 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, 0 < c → c ≤ c₀ →
      ∀ (i o : ℝ) (hm : WideScreenFrequencySmooth i o (inverseMatrix g)),
      ∀ (inn out : ℝ), 0 ≤ inn → inn < out → out ≤ D → ∀ hη : 0 < c * κ * δ ^ 2,
      ∀ M : ℝ, 0 ≤ M →
        (∀ k J I, ∀ y ∈ (Metric.closedBall (0 : E) (1 / 4) ×ˢ Metric.sphere (0 : E) 1) ×ˢ Metric.sphere (0 : E) 1,
          ‖actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I y‖ ≤ M) →
      ∀ z : ProjectionSchwartzMatrix,
        let N := originalFarPatchFourierWeight g a ϑ κ δ i o hm hη inn out z
        Integrable N ∧ (tau ^ 8)⁻¹ • ∫ x, N x = actualFarPatchEnergy g a ϑ κ δ b i o hm hη inn out z := by
  classical
  obtain ⟨c₀, b, hc₀, hb, exactness⟩ := exists_actualThinFar_exact_physicalQuotient hK hFrame D hD
  refine ⟨c₀, b, hc₀, hb, ?_⟩
  intro g hg a odd hom ha ϑ hϑ cut flat κ hκ hs δ hδ hd c hc hc' i o hm inn out hin hio hout hη M hM bound z N
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
      have eq := (exactness g hg a odd hom (ha.of_le (by simp)) ϑ cut flat κ hκ hs δ hδ hd c hc hc' i o hm
        inn out hin hio hout k J I p q (-(p + q)) hp hq (neg_ne_zero.mpr hr) (add_neg_cancel (p + q)) hη).2
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

end Burnett.V10.OriginalGaugeCompatibility
