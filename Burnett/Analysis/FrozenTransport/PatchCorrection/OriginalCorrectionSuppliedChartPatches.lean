import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualPatchFourierSum
import Burnett.Analysis.FrozenTransport.PatchCorrection.IntrinsicCommonWideCorrectionJets
import Burnett.Analysis.TransportPatches.OriginalTransportPatchFamily
import Burnett.Analysis.TransportPatches.ScreenWideSupport

set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 6700

noncomputable section

namespace Burnett.V11

open Set Filter Metric MeasureTheory Matrix
open Burnett.Geometry Burnett.P01 Burnett.C02 Burnett.C03 Burnett.V06 Burnett.V08 Burnett.RicciSymbol
open ConnectionDifference InverseField ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.V10.OriginalGaugeCompatibility
open Burnett.A02.FrequencySplit (E Joint tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix metricDensity)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Topology ENNReal Matrix BigOperators ComplexConjugate

open private chartInverseMetric_isUnit from Burnett.Analysis.TransportPatches.ActualWideScreenLipschitz

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The two literal Fourier corrections on the supplied receiving patches.
The joint screen and geometric invertibility window are fixed before the
thin width. The profiles and correction constant are then fixed before `ℓ`.
The coefficient and source inputs are those of the supplied C03 family. -/
theorem exists_originalCorrectionPatchFourierTail_of_suppliedChartPatches
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hSig : HasLorentzSignature B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (V K : Set E) (hV : IsOpen V) (hK : IsCompact K)
    (hKV : K ⊆ V) (hVU : V ⊆ c.chart.target)
    (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (e : ℕ → ℝ) (he₀ : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (Msrc Ccoeff : ℝ) (hMsrc : 0 ≤ Msrc) (hCcoeff : 0 ≤ Ccoeff)
    (Cp : {p : ℝ // 1 < p} → ℝ) (hCp : ∀ p, 0 ≤ Cp p)
    (wi wo : ℝ) (joint : HasJointWideScreen B c wi wo V)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a (V ×ˢ {ξ : E | ξ ≠ 0}))
    (odd : ∀ x ∈ K, ∀ ξ : E, a (x, -ξ) = -a (x, ξ))
    (hom : ∀ x ∈ K, ∀ t : ℝ, 0 < t → ∀ ξ : E, a (x, t • ξ) = t * a (x, ξ))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (cut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (flat : ∀ t : ℝ, 0 ≤ t → t ≤ 1 / 4 → ϑ t = 1) (bounded : ∀ t : ℝ, |ϑ t| ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hsmall : κ < 1 / 16) (Dwidth : ℝ) (hDwidth : 0 ≤ Dwidth) :
    let g₀ := metricComponents (fixedForm B c)
    let m := chartInverseMetric B c
    let wide (x : E) (hx : x ∈ K) : WideScreenFrequencySmooth wi wo (m x) :=
      wideScreen_frequencySmooth_of_joint joint (hKV hx)
    ∃ c₀ εwin : ℝ, 0 < c₀ ∧ 0 < εwin ∧
      (∀ x ∈ K, ∀ ξ : Burnett.RicciSymbol.Covector, ξ ⬝ᵥ ξ = 1 → |symbolNorm (m x) ξ| < εwin →
        screenSecondDirection (m x) ξ ≠ 0 ∧
        IsUnit (screenMetricExtension (m x) (screenDirectionProjection (m x) ξ)).det) ∧
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → ∀ (cThin : ℝ) (hcThin : 0 < cThin), cThin ≤ c₀ →
      ∀ inn out : ℝ, 0 ≤ inn → inn < out → out ≤ Dwidth →
      let η := cThin * κ * δ ^ 2
      let hη : 0 < η := mul_pos (mul_pos hcThin hκ) (pow_pos hδ _)
      ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ℓ : ℝ) (hℓ : 0 < ℓ) (s : Finset LatticeIndex) (dχ : LatticeIndex → D) (ψ : LatticeIndex → E → ℝ)
        (hd : ∀ j, tsupport (dχ j : E → ℝ) ⊆ c.chart.target),
      let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
      let z (n : ℕ) (j : LatticeIndex) := receivingCutoffFluctuation B g hB hg c (dχ j) (hd j) (σ n)
      ∀ (hPatch : ∀ j ∈ s, P j ⊆ K) (W : ℝ), (∑ j ∈ s, (volume (P j)).toReal) ≤ W →
      (∀ j ∈ s, ∀ᶠ n in atTop,
        let m₀ := m (patchCenter ℓ j)
        ∃ (A : ProjectedSourceCoefficients) (v : Index → Index → SchwartzMap E ℝ),
          (∀ i k x, A.entry i k x = ((m₀ i k + v i k x : ℝ) : ℂ)) ∧
          (∀ i k x, v i k x = correctionCoefficientPart (ψ j)
            (matrixInverse ∘ metricComponents (fixedForm (g (σ n)) c)) m₀ x i k) ∧
          (∀ i k, v i k = v k i) ∧
          (∀ i k x, |v i k x| ≤ Ccoeff * (ℓ + e (σ n))) ∧
          (∀ i k x, ‖fderiv ℝ (v i k : E → ℝ) x‖ ≤ 4 * Ccoeff * (1 + e (σ n) / ℓ)) ∧
          ‖projectedSourceDivergenceL2 A (projectionFullSchwartz (z n j))‖ ≤
            Msrc * (volume (P j) ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n)) ∧
          ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val (z n j) (P j)
            (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ))) →
      let x (j : s) := patchCenter ℓ j
      let hc (j : s) : x j ∈ K := hPatch j j.property (mem_closedBall_self (mul_nonneg (by norm_num) hℓ.le))
      let far (n : ℕ) (j : s) := originalFarPatchFourierWeight (g₀ (x j)) (fun ξ => a (x j, ξ))
        ϑ κ δ wi wo (wide (x j) (hc j)) hη inn out (z n j)
      let gauge (n : ℕ) (j : s) := originalGaugePhysicalNumerator ϑ κ (g₀ (x j)) (fun ξ => a (x j, ξ))
        (thinScreenAngular (m (x j)) wi wo (wide (x j) (hc j)) hη inn out).matrix (z n j)
      let I (A : Joint → ℂ) := ((tau^8)⁻¹ : ℝ) • (∫ y, A y)
      ∀ ε > 0, ∀ᶠ n in atTop, (∀ j : s, Integrable (far n j) ∧ Integrable (gauge n j)) ∧
        (∑ j : s, (‖I (far n j)‖ + ‖I (gauge n j)‖)) ≤ C * ℓ * W + ε := by
  classical
  intro g₀ m wide
  have hKU : K ⊆ c.chart.target := hKV.trans hVU
  obtain ⟨hCompact, hFrame⟩ := compact_chartInverseMetric_family B hB hSig c K hK hKU
  have hInv (Q : Tensor2) (hQ : Q ∈ m '' K) : IsUnit (Matrix.det Q) := by
    obtain ⟨y, hy, rfl⟩ := hQ
    exact chartInverseMetric_isUnit B hSig.isNondegenerate c (hKU hy)
  obtain ⟨εwin, hεwin, hScreen⟩ := exists_uniform_wide_screen_invertibility (m '' K) hCompact hInv hFrame
  obtain ⟨_, _, _, _, _, selectGuard⟩ := exists_originalFarPatch_selectGuard
  obtain ⟨c₀, b, hc₀, hb, guard⟩ := selectGuard hCompact hFrame Dwidth hDwidth
  refine ⟨c₀, εwin, hc₀, hεwin, fun x hx => hScreen (m x) ⟨x, hx, rfl⟩, ?_⟩
  intro δ hδ hd₁ cThin hcThin hdThin inn out hin hio hout η hη
  have hFiber (y : E) (hy : y ∈ K) : ContDiffOn ℝ ∞ (fun ξ => a (y, ξ)) ({0}ᶜ : Set E) := by
    have smooth : ContDiff ℝ ∞ (fun ξ : E => (y, ξ)) := contDiff_const.prodMk contDiff_id
    exact ha.comp smooth.contDiffOn (fun _ hξ => ⟨hKV hy, hξ⟩)
  have hPhase (y : E) (hy : y ∈ K) : ActualFarPhaseIdentities (g₀ y) (fun ξ => a (y, ξ))
      ϑ κ δ b wi wo (wide y hy) hη inn out :=
    (guard (g₀ y) ⟨y, hy, rfl⟩ (fun ξ => a (y, ξ)) (fun ξ _ => odd y hy ξ)
      (fun t ht ξ _ => hom y hy t ht ξ) (hFiber y hy) ϑ hϑ cut flat κ hκ hsmall δ hδ hd₁
      cThin hcThin hdThin wi wo (wide y hy) inn out hin hio hout hη).1
  obtain ⟨S, same, jets⟩ := exists_intrinsicCorrection_jets_of_jointWideScreen B hB hSig c V K
    hV hK hKV hVU wi wo joint a ha ϑ hϑ κ hκ δ b hη inn out
  obtain ⟨N, Co, Cw, hCo, hCw, correction⟩ := exists_actualCorrections_consume_sameProjectedPatch
  obtain ⟨J, hJ, hJet⟩ := jets N
  obtain ⟨J₀, hJ₀, hJet₀⟩ := jets 0
  let p₂ : {p : ℝ // 1 < p} := ⟨2, by norm_num⟩
  let p₄ : {p : ℝ // 1 < p} := ⟨4, by norm_num⟩
  let Q := 1 + Co * J + 2 * Cw * J + Msrc + 4 * Ccoeff + 4 * Cp p₂ + 4 * Cp p₄
  have hQ : 1 ≤ Q ∧ Co * J ≤ Q ∧ 2 * Cw * J ≤ Q ∧ Msrc ≤ Q ∧ Ccoeff ≤ Q ∧ 4 * Ccoeff ≤ Q ∧
      Cp p₂ ≤ Q / 4 ∧ Cp p₄ ≤ Q / 4 ∧ Cp p₄ ≤ Q := by
    dsimp [Q]
    have h₀ := mul_nonneg hCo hJ
    have h₁ := mul_nonneg hCw hJ
    have h₂ := hCp p₂
    have h₄ := hCp p₄
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith only [h₀, h₁, h₂, h₄, hMsrc, hCcoeff]
  obtain ⟨hQ₁, hQo, hQw, hQsrc, hQcoeff, hQcoeff₄, hQ₂, hQ₄, hQ₄'⟩ := hQ
  let C := (16 ^ 3 : ℝ) * (6 * Q ^ 5)
  have hQ₀ : 0 ≤ Q := zero_le_one.trans hQ₁
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ℓ hℓ s dχ ψ hd P z hPatch W hVol source x hc far gauge I ε hε
  have hCenters (j : LatticeIndex) (hj : j ∈ s) : patchCenter ℓ j ∈ K :=
    hPatch j hj (mem_closedBall_self (by positivity))
  let G := originalMetricGaugeEnergy ϑ κ g₀ a S
  let F := originalMetricFarEnergy g₀ a ϑ κ δ b wi wo K wide hη inn out
  have pointBound : ∀ᶠ n in atTop, ∀ j ∈ s,
      ‖G (patchCenter ℓ j) (z n j)‖ + ‖F (patchCenter ℓ j) (z n j)‖ ≤
        C * (volume (P j)).toReal * Burnett.C04.correctionEnvelope ℓ (e (σ n)) := by
    filter_upwards [(s.eventually_all).2 source] with n hn
    intro j hj
    let y := patchCenter ℓ j
    let u := e (σ n)
    have hy : y ∈ K := hCenters j hj
    have hu : 0 ≤ u := he₀ (σ n)
    obtain ⟨A, v, hA, _, symm, mag, slope, hSrc, lp⟩ := hn j hj
    have hFactor : 0 ≤ 1 + u / ℓ := by positivity
    have hSource : ‖projectedSourceDivergenceL2 A (projectionFullSchwartz (z n j))‖ ≤
        Q * (volume (P j) ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * u) :=
      hSrc.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hQsrc ENNReal.toReal_nonneg) (by positivity))
    have controls : GaugePatchCoefficientBounds Q ℓ u v (z n j) (P j) :=
      ⟨fun i k x => (mag i k x).trans (mul_le_mul_of_nonneg_right hQcoeff (by positivity)),
        fun i k x => (slope i k x).trans (mul_le_mul_of_nonneg_right hQcoeff₄ hFactor),
        ⟨_, (lp p₂).mono le_rfl (mul_le_mul_of_nonneg_right hQ₂ hFactor)⟩,
        (lp p₄).mono (mul_le_mul_of_nonneg_right hQ₄' hu) (mul_le_mul_of_nonneg_right hQ₄ hFactor)⟩
    have hGa : G y (z n j) = originalGaugePatchEnergy ϑ κ (m y) (metricDensity (g₀ y))
        (fun ξ => a (y, ξ)) (gaugeFrozenContraction (m y))
        (thinScreenAngular (m y) wi wo (wide y hy) hη inn out).matrix (z n j) := by
      change originalGaugePatchEnergy ϑ κ (m y) (metricDensity (g₀ y))
        (fun ξ => a (y, ξ)) (gaugeFrozenContraction (m y)) (S y) (z n j) = _
      rw [same y hy]
    have hFa : F y (z n j) = actualFarPatchEnergy (g₀ y) (fun ξ => a (y, ξ)) ϑ κ δ b wi wo (wide y hy)
        hη inn out (z n j) := dif_pos hy
    have compat := hJet y hy
    simp only [same y hy] at compat
    change ‖G y (z n j)‖ + ‖F y (z n j)‖ ≤ _
    rw [hGa, hFa]
    exact correction (g₀ y) (fun ξ => a (y, ξ)) ϑ (hFiber y hy) (odd y hy) (hom y hy) cut κ hκ hsmall δ b wi wo
      (wide y hy) hη inn out J hJ compat v A (z n j) (P j) Q ℓ u hQ₁ hℓ hu hQo hQw symm hA controls hSource
  have hLim := Burnett.C04.tendsto_correctionEnvelope ℓ _ (he.comp hσ.tendsto_atTop)
  have hSmall := (tendsto_order.1 (hLim.const_mul (C * W))).2 (C * W * ℓ + ε) (by linarith)
  have hTranspose (y : E) (_ : y ∈ K) : (g₀ y)ᵀ = g₀ y :=
    funext fun i => funext fun j => hSig.isSymmetric (c.chart.symm y) _ _
  filter_upwards [pointBound, hSmall] with n hn hsmalln
  let env := Burnett.C04.correctionEnvelope ℓ (e (σ n))
  have henv : 0 ≤ env := by
    dsimp only [env, Burnett.C04.correctionEnvelope]
    have := he₀ (σ n)
    positivity
  have hEnergy : (∑ j ∈ s, (‖G (patchCenter ℓ j) (z n j)‖ + ‖F (patchCenter ℓ j) (z n j)‖)) ≤ C * ℓ * W + ε := by
    calc
      _ ≤ ∑ j ∈ s, C * (volume (P j)).toReal * env := Finset.sum_le_sum hn
      _ = C * (∑ j ∈ s, (volume (P j)).toReal) * env := by rw [Finset.mul_sum, Finset.sum_mul]
      _ ≤ C * W * env := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVol hC) henv
      _ ≤ _ := by simpa only [env, Function.comp_apply, mul_comm ℓ W, mul_assoc] using hsmalln.le
  have realZ (j : LatticeIndex) (_ : j ∈ s) (i k : Index) (y : E) : conj (z n j i k y) = z n j i k y :=
    Complex.conj_ofReal _
  have h := originalCorrectionFourierSum_of_sharedBudget g₀ K hTranspose a hFiber odd hom ϑ hϑ cut bounded
    κ hκ hsmall δ b wi wo wide hη inn out S same hPhase J₀ hJ₀ (fun y hy i j k => (hJet₀ y hy i j k).2)
    ℓ s hCenters (z n) realZ _ hEnergy
  let gauge₀ (j : LatticeIndex) := originalGaugePhysicalNumerator ϑ κ (g₀ (patchCenter ℓ j))
    (fun ξ => a (patchCenter ℓ j, ξ)) (S (patchCenter ℓ j)) (z n j)
  let far₀ (j : LatticeIndex) : Joint → ℂ := if hy : patchCenter ℓ j ∈ K then
    originalFarPatchFourierWeight (g₀ (patchCenter ℓ j)) (fun ξ => a (patchCenter ℓ j, ξ))
      ϑ κ δ wi wo (wide (patchCenter ℓ j) hy) hη inn out (z n j) else 0
  have hF (j : s) : far₀ j = far n j := dif_pos (hc j)
  have hG (j : s) : gauge₀ j = gauge n j := by
    change originalGaugePhysicalNumerator ϑ κ (g₀ (x j)) (fun ξ => a (x j, ξ)) (S (x j)) (z n j) = _
    rw [same (x j) (hc j)]
  have hInt : ∀ j ∈ s, Integrable (gauge₀ j) ∧ Integrable (far₀ j) := h.1
  refine ⟨fun j => ⟨?_, ?_⟩, ?_⟩
  · rw [← hF j]
    exact (hInt j j.property).2
  · rw [← hG j]
    exact (hInt j j.property).1
  have hSum : (∑ j ∈ s, (‖I (gauge₀ j)‖ + ‖I (far₀ j)‖)) ≤ C * ℓ * W + ε := h.2
  rw [← Finset.sum_coe_sort] at hSum
  simpa only [hF, hG, add_comm] using hSum

end Burnett.V11
