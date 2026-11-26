import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualCorrectionPatchConsumer

set_option autoImplicit false
set_option maxHeartbeats 8500000
set_option maxRecDepth 6000

noncomputable section

namespace Burnett.V11

open Set Filter Metric MeasureTheory Matrix Burnett.P01 Burnett.RicciSymbol Burnett.V08 Burnett.C02 Burnett.C03
open Burnett.Geometry.InverseField Burnett.Geometry.CurvatureDifference Burnett.Geometry.ConnectionDifference
open Burnett.V10.OriginalGaugeCompatibility
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.TransportWardSymbol (metricDensity inverseMatrix)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ContDiff Topology ENNReal Matrix BigOperators

def originalMetricFarEnergy (g₀ : E → Tensor2) (a : Joint → ℝ) (ϑ : ℝ → ℝ) (κ δ b i o : ℝ) (K : Set E)
    (wide : ∀ x ∈ K, WideScreenFrequencySmooth i o (inverseMatrix (g₀ x))) {η : ℝ} (hη : 0 < η)
    (inn out : ℝ) (x : E) (z : ProjectionSchwartzMatrix) : ℂ := by
  classical
  exact if hx : x ∈ K then actualFarPatchEnergy (g₀ x) (fun ξ => a (x, ξ)) ϑ κ δ b i o
    (wide x hx) hη inn out z else 0

/-- Choose the original source constants before receiving the C02 wide
screen. One partition and its whole-sequence Lp bounds then serve C02 and
both corrections. The sum is controlled along the original subsequence. -/
theorem exists_commonFarGauge_patchBudget
    (U K Kplus : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKplus : IsCompact Kplus)
    (hNested : K ⊆ interior Kplus) (hKU : Kplus ⊆ U) (g₀ : E → Tensor2) (g : ℕ → E → Tensor2)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U) (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hND₀ : ∀ x ∈ U, Matrix.det (g₀ x) ≠ 0) (hND : ∀ n x, x ∈ U → Matrix.det (g n x) ≠ 0)
    (hSym₀ : ∀ x ∈ U, IsSymmetricTensor (g₀ x)) (hSym : ∀ n x, x ∈ U → IsSymmetricTensor (g n x))
    (hVac : ∀ n x, x ∈ U → ∀ i j, coordinateRicci (fun y => christoffel (projectedChartInverse (g n) y) (coordinateJet (g n) y)) x i j = 0)
    (hConv : TendstoUniformlyOn g g₀ atTop Kplus) (D : ℝ) (hD : 0 ≤ D) (hJet : ∀ n x, x ∈ Kplus → ‖coordinateJet (g n) x‖ ≤ D)
    (e : ℕ → ℝ) (he₀ : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0)) (hError : ∀ n x, x ∈ Kplus → ‖g n x - g₀ x‖ ≤ e n)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ (ℓ₀ : ℝ) (Ccut : ℕ → ℝ) (Cp : {p : ℝ // 1 < p} → ℝ),
    0 < ℓ₀ ∧ (∀ k, 0 ≤ Ccut k) ∧ (∀ p, 0 ≤ Cp p) ∧
    ∀ (ϑ : ℝ → ℝ), (∀ t : ℝ, 1 ≤ t → ϑ t = 0) → ∀ κ : ℝ, 0 < κ → κ < 1 / 16 →
    ∀ (a : Joint → ℝ), (∀ x ∈ Kplus, ContDiffOn ℝ ∞ (fun ξ => a (x, ξ)) {ξ : E | ξ ≠ 0}) →
    (∀ x ∈ Kplus, ∀ ξ, a (x, -ξ) = -a (x, ξ)) →
    (∀ x ∈ Kplus, ∀ t : ℝ, 0 < t → ∀ ξ, a (x, t • ξ) = t * a (x, ξ)) →
    ∀ (δ b i o : ℝ) (wide : ∀ x ∈ Kplus, WideScreenFrequencySmooth i o (inverseMatrix (g₀ x))),
    ∀ {η : ℝ} (hη : 0 < η) (inn out : ℝ),
    ∀ (S : E → GaugeScreen), (∀ x (hx : x ∈ Kplus),
      S x = (thinScreenAngular (inverseMatrix (g₀ x)) i o (wide x hx) hη inn out).matrix) →
    (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x (hx : x ∈ Kplus), ∀ k j l,
      GaugeProfileBound N M (gaugeTriadAngularProfile ϑ κ (inverseMatrix (g₀ x)) (metricDensity (g₀ x))
        (fun ξ => a (x, ξ)) (gaugeFrozenContraction (inverseMatrix (g₀ x))) (S x) k l j) ∧
      GaugeProfileBound N M (actualFarAngularProfile (g₀ x) (fun ξ => a (x, ξ)) ϑ κ δ b i o
        (wide x hx) hη inn out k j l)) →
    let G := originalMetricGaugeEnergy ϑ κ g₀ a S
    let F := originalMetricFarEnergy g₀ a ϑ κ δ b i o Kplus wide hη inn out
    ∃ B : ℝ, 1 ≤ B ∧
      ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ →
      ∃ (s : Finset LatticeIndex) (χ χplus : LatticeIndex → E → ℝ),
      let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
      let C := (16 ^ 3 : ℝ) * (6 * B ^ 5)
      (∀ x ∈ thickening ℓ K, ∑ j ∈ s, χ j x ^ 3 = 1) ∧
      (∀ x ∈ thickening ℓ K, ∀ v : E, ∑ j ∈ s, χ j x ^ 2 * fderiv ℝ (χ j) x v = 0) ∧
      (∑ j ∈ s, volume (W j)) ≤ ((17 ^ 4 : ℕ) : ℝ≥0∞) * volume Kplus ∧
      (∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ ContDiff ℝ ∞ (χplus j) ∧
        (∀ x, 0 ≤ χ j x ∧ χplus j x ∈ Icc (0 : ℝ) 1) ∧
        tsupport (χ j) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧
        tsupport (χplus j) ⊆ W j ∧ W j ⊆ interior Kplus ∧
        (∀ x ∈ thickening ℓ (tsupport (χ j)), χplus j x = 1) ∧
        (∀ k x, ‖iteratedFDeriv ℝ k (χ j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k ∧
          ‖iteratedFDeriv ℝ k (χplus j) x‖ ≤ Ccut k * ℓ⁻¹ ^ k)) ∧
      (∀ j ∈ s, ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
        (∀ i k x, z i k x = ((χ j x * (g n x i k - g₀ x i k) : ℝ) : ℂ)) ∧
        ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j) (Cp p * e n) (Cp p * (1 + e n / ℓ))) ∧
      (∀ᶠ n in atTop, ∀ j ∈ s,
        let x₀ := patchCenter ℓ j
        let m := matrixInverse (g₀ x₀)
        ∃ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) (d : Index → Index → SchwartzMap E ℝ),
          (∀ i k x, z i k x = ((χ j x * (g (σ n) x i k - g₀ x i k) : ℝ) : ℂ)) ∧
          (∀ i k x, A.entry i k x = ((m i k + d i k x : ℝ) : ℂ)) ∧
          (∀ i k x, d i k x = correctionCoefficientPart (χplus j) (matrixInverse ∘ g (σ n)) m x i k) ∧
          (∀ i k, d i k = d k i) ∧
          GaugePatchCoefficientBounds B ℓ (e (σ n)) d z (W j) ∧
          (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
            B * (volume (W j) ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n))) ∧
          (∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j) (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ))) ∧
          ‖G x₀ z‖ + ‖F x₀ z‖ ≤ C * (volume (W j)).toReal * Burnett.C04.correctionEnvelope ℓ (e (σ n))) ∧
      ∀ ε > 0, ∀ᶠ n in atTop, ∀ Z : LatticeIndex → ProjectionSchwartzMatrix,
        (∀ j ∈ s, ∀ i k x, Z j i k x = ((χ j x * (g (σ n) x i k - g₀ x i k) : ℝ) : ℂ)) →
        (∑ j ∈ s, (‖G (patchCenter ℓ j) (Z j)‖ + ‖F (patchCenter ℓ j) (Z j)‖)) ≤
          C * (17 ^ 4 : ℝ) * (volume Kplus).toReal * ℓ + ε := by
  classical
  obtain ⟨ℓ₀, Msrc, Ccoeff, Ccut, Cp, hℓ₀, hMsrc, hCcoeff, hCcut, hCp, patches⟩ :=
    exists_original_projectedPatchSource_family U K Kplus hU hK hKplus hNested hKU g₀ g hg₀ hg hND₀ hND
      hSym₀ hSym hVac hConv D hD hJet e he₀ he hError
  refine ⟨ℓ₀, Ccut, Cp, hℓ₀, hCcut, hCp, ?_⟩
  intro ϑ hcut κ hκ hsmall a ha odd hom δ b i o wide η hη inn out S same jets G F
  obtain ⟨N, Co, Cw, hCo, hCw, correction⟩ := exists_actualCorrections_consume_sameProjectedPatch
  obtain ⟨M, hM, jet⟩ := jets N
  let p₂ : {p : ℝ // 1 < p} := ⟨2, by norm_num⟩
  let p₄ : {p : ℝ // 1 < p} := ⟨4, by norm_num⟩
  let B := 1 + Co * M + 2 * Cw * M + Msrc + 4 * Ccoeff + 4 * Cp p₂ + 4 * Cp p₄
  have hBudget : 1 ≤ B ∧ Co * M ≤ B ∧ 2 * Cw * M ≤ B ∧ Msrc ≤ B ∧ Ccoeff ≤ B ∧ 4 * Ccoeff ≤ B ∧
      Cp p₂ ≤ B / 4 ∧ Cp p₄ ≤ B / 4 ∧ Cp p₄ ≤ B := by
    dsimp [B]
    have h₀ := mul_nonneg hCo hM
    have h₁ := mul_nonneg hCw hM
    have h₂ := hCp p₂
    have h₄ := hCp p₄
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> nlinarith only [h₀, h₁, h₂, h₄, hMsrc, hCcoeff]
  obtain ⟨hB, hBo, hBw, hBsrc, hBc, hBc₄, hB₂, hB₄, hB₄'⟩ := hBudget
  refine ⟨B, hB, ?_⟩
  intro ℓ hℓ hsmallℓ
  obtain ⟨s, χ, χplus, cube, cancel, vol, windows, original⟩ := patches ℓ hℓ hsmallℓ
  let W (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
  let C := (16 ^ 3 : ℝ) * (6 * B ^ 5)
  have forC02 (j : LatticeIndex) (hj : j ∈ s) : ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
      (∀ i k x, z i k x = ((χ j x * (g n x i k - g₀ x i k) : ℝ) : ℂ)) ∧
      ∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j) (Cp p * e n) (Cp p * (1 + e n / ℓ)) := by
    filter_upwards [original] with n hn
    obtain ⟨_, z, _, _, _, _, _, _, hz, _, lp⟩ := hn j hj
    exact ⟨z, hz, lp⟩
  have both : ∀ᶠ n in atTop, ∀ j ∈ s,
      let x₀ := patchCenter ℓ j
      let m := matrixInverse (g₀ x₀)
      ∃ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) (d : Index → Index → SchwartzMap E ℝ),
        (∀ i k x, z i k x = ((χ j x * (g (σ n) x i k - g₀ x i k) : ℝ) : ℂ)) ∧
        (∀ i k x, A.entry i k x = ((m i k + d i k x : ℝ) : ℂ)) ∧
        (∀ i k x, d i k x = correctionCoefficientPart (χplus j) (matrixInverse ∘ g (σ n)) m x i k) ∧
        (∀ i k, d i k = d k i) ∧ GaugePatchCoefficientBounds B ℓ (e (σ n)) d z (W j) ∧
        (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
          B * (volume (W j) ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n))) ∧
        (∀ p : {p : ℝ // 1 < p}, ProjectedPatchLpBounds p.val z (W j) (Cp p * e (σ n)) (Cp p * (1 + e (σ n) / ℓ))) ∧
        ‖G x₀ z‖ + ‖F x₀ z‖ ≤ C * (volume (W j)).toReal * Burnett.C04.correctionEnvelope ℓ (e (σ n)) := by
    filter_upwards [hσ.tendsto_atTop.eventually original] with n hn
    intro j hj x₀ m
    obtain ⟨A, z, d, hA, hd, symm, mag, slope, hz, source, lp⟩ := hn j hj
    have hx : x₀ ∈ Kplus := interior_subset ((windows j hj).2.2.2.2.2.1 (mem_closedBall_self (by positivity)))
    have he' : 0 ≤ e (σ n) := he₀ (σ n)
    have hFactor : 0 ≤ 1 + e (σ n) / ℓ := by positivity
    have hSource : ‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
        B * (volume (W j) ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e (σ n)) :=
      source.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hBsrc ENNReal.toReal_nonneg) (by positivity))
    have controls : GaugePatchCoefficientBounds B ℓ (e (σ n)) d z (W j) :=
      ⟨fun i k x => (mag i k x).trans (mul_le_mul_of_nonneg_right hBc (by positivity)),
        fun i k x => (slope i k x).trans (mul_le_mul_of_nonneg_right hBc₄ hFactor),
        ⟨_, (lp p₂).mono le_rfl (mul_le_mul_of_nonneg_right hB₂ hFactor)⟩,
        (lp p₄).mono (mul_le_mul_of_nonneg_right hB₄' he') (mul_le_mul_of_nonneg_right hB₄ hFactor)⟩
    have gAlign : G x₀ z = originalGaugePatchEnergy ϑ κ (inverseMatrix (g₀ x₀)) (metricDensity (g₀ x₀))
        (fun ξ => a (x₀, ξ)) (gaugeFrozenContraction (inverseMatrix (g₀ x₀)))
        (thinScreenAngular (inverseMatrix (g₀ x₀)) i o (wide x₀ hx) hη inn out).matrix z := by
      change originalGaugePatchEnergy ϑ κ (inverseMatrix (g₀ x₀)) (metricDensity (g₀ x₀))
        (fun ξ => a (x₀, ξ)) (gaugeFrozenContraction (inverseMatrix (g₀ x₀))) (S x₀) z = _
      rw [same x₀ hx]
    have fAlign : F x₀ z = actualFarPatchEnergy (g₀ x₀) (fun ξ => a (x₀, ξ)) ϑ κ δ b i o (wide x₀ hx) hη inn out z := dif_pos hx
    have compat := jet x₀ hx
    simp only [same x₀ hx] at compat
    refine ⟨A, z, d, hz, hA, hd, symm, controls, hSource, lp, ?_⟩
    rw [gAlign, fAlign]
    exact correction (g₀ x₀) (fun ξ => a (x₀, ξ)) ϑ (ha x₀ hx) (odd x₀ hx) (hom x₀ hx) hcut κ hκ hsmall δ b i o
      (wide x₀ hx) hη inn out M hM compat d A z (W j) B ℓ (e (σ n)) hB hℓ he' hBo hBw symm hA controls hSource
  refine ⟨s, χ, χplus, cube, cancel, vol, windows, forC02, both, ?_⟩
  intro ε hε
  let V := (17 ^ 4 : ℝ) * (volume Kplus).toReal
  have hVol : (∑ j ∈ s, (volume (W j)).toReal) ≤ V := by
    have h := ENNReal.toReal_mono (ENNReal.mul_lt_top (by norm_num) hKplus.measure_lt_top).ne vol
    rw [ENNReal.toReal_sum (fun _ _ => (isCompact_closedBall _ _).measure_lt_top.ne), ENNReal.toReal_mul] at h
    dsimp only [V]
    exact_mod_cast h
  have hLim := Burnett.C04.tendsto_correctionEnvelope ℓ _ (he.comp hσ.tendsto_atTop)
  have small := (tendsto_order.1 (hLim.const_mul (C * V))).2 (C * V * ℓ + ε) (by linarith)
  filter_upwards [both, small] with n hn hsmalln
  intro Z hZ
  let env := Burnett.C04.correctionEnvelope ℓ (e (σ n))
  have henv : 0 ≤ env := by
    dsimp only [env, Burnett.C04.correctionEnvelope]
    have := he₀ (σ n)
    positivity
  have one (j : LatticeIndex) (hj : j ∈ s) : ‖G (patchCenter ℓ j) (Z j)‖ + ‖F (patchCenter ℓ j) (Z j)‖ ≤
      C * (volume (W j)).toReal * env := by
    obtain ⟨_, z, _, hz, _, _, _, _, _, _, hzBound⟩ := hn j hj
    have sameZ : Z j = z := by funext i k; ext x; rw [hZ j hj i k x, hz i k x]
    rw [sameZ]
    exact hzBound
  calc
    _ ≤ ∑ j ∈ s, C * (volume (W j)).toReal * env := Finset.sum_le_sum one
    _ = C * (∑ j ∈ s, (volume (W j)).toReal) * env := by rw [Finset.mul_sum, Finset.sum_mul]
    _ ≤ C * V * env := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hVol (by dsimp [C]; positivity)) henv
    _ ≤ _ := by simpa only [C, V, env, Function.comp_apply, mul_assoc] using hsmalln.le

end Burnett.V11
