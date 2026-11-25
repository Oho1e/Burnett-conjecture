import Burnett.Analysis.TransportPatches.FrozenErrorCompression
import Burnett.Analysis.TransportPatches.WholeCosphereDefectNorm

/-! Apply the frozen principal estimates under the original weighted norm integral. -/

set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 7200000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.V06
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.Overlap
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector)
open Burnett.P01 (principalGaugeProjectionMatrix)
open Burnett.X02.SobolevTestJet (D)
open scoped BigOperators ContDiff ComplexConjugate ComplexOrder Manifold Matrix MatrixOrder Topology

local notation "E" => CoordinateSpace
local notation "V" => OrderedPair → ℂ
local notation "Mat" => Matrix OrderedPair OrderedPair ℂ

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

private theorem complexWideScreen_zero (inner outer : ℝ) (m : Tensor2) (q : Covector) :
    complexWideScreen inner outer m 0 q = 0 := by
  have hr : tensorRe (0 : ComplexTensor2) = 0 := rfl
  have hi : tensorIm (0 : ComplexTensor2) = 0 := rfl
  funext i j
  unfold complexWideScreen
  rw [hr, hi]
  apply Complex.ext <;> simp [globalAngularScreenSymbol, frozenScreenSymbol, frozenScreenProjection]

private theorem weightedTrace_re (N P : Mat) (w : ℝ) :
    (P * (w : ℂ) • N * Pᴴ).trace.re = w * (P * N * Pᴴ).trace.re := by
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Each of the two whole-space norm integrands keeps the precise chart
volume reweighting and original cutoff. The a.e. bound is on the very same
trace measure and uses the actual Ricci constraint also off the null shell. -/
theorem exists_actualFrozenScreen_originalWeightedCompression
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (σ : ℕ → ℕ) (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ inner outer C : ℝ, 0 < inner ∧ inner < outer ∧ 0 ≤ C ∧
      ∀ x₀ ∈ K, ∀ ℓ : ℝ, (∀ x ∈ K, ‖x - x₀‖ ≤ ℓ) → ℓ ≤ 1 →
      let m := chartInverseMetric B c x₀
      let τ := A.control.restrict (amplitudeCosphereWindow r (c.chart.symm '' K))
      ∀ᵐ p ∂τ, let q := atlasChartUnitCovector c p
        let ξ : E := WithLp.toLp 2 q
        let P := principalGaugeProjectionMatrix ξ
        let S := complexWideScreen inner outer m
        ∀ (χ : D) (T₁ T₂ : ClassicalMatrixMultiplier OrderedPair),
          (∀ v : V, let J := tensorOfVector (P *ᵥ v)
            tensorOfVector (T₁.principal ξ *ᵥ v) = J - S J q) →
          (∀ v : V, let J := tensorOfVector (P *ᵥ v)
            tensorOfVector (T₂.principal ξ *ᵥ v) = (normalizedFrozenPhase m ξ : ℂ) • S J q) →
          let W := ((χ : E → ℝ) (fixedChartPhase c p.val).1)^2 * ‖ξ‖^2 *
            (P * chartLebesgueAmplitude B c A p * Pᴴ).trace.re
          globalDefectNormIntegrand B c χ T₁ A p ≤ (16 * (C * ℓ)^2) * W ∧
          globalDefectNormIntegrand B c χ T₂ A p ≤ (16 * (C * ℓ)^2) * W := by
  obtain ⟨i, o, C, hi, hIO, hC, hComp⟩ :=
    exists_actualFrozenScreen_traceCompression (r := r) B hB hSig c K hK hConv hKU
  refine ⟨i, o, C, hi, hIO, hC, ?_⟩
  intro x₀ hx₀ ℓ hℓ hℓ₁ m τ
  have hImage : IsCompact (c.chart.symm '' K) := hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKU)
  have hWindow := measurableSet_amplitudeCosphereWindow r hImage.isClosed.measurableSet
  filter_upwards [ae_restrict_mem (μ := A.control) hWindow, ae_restrict_of_ae hA.2.2.2.2.2] with p hp hData
  intro q ξ P S χ T₁ T₂ hT₁ hT₂ W
  change projection p ∈ c.chart.symm '' K at hp
  obtain ⟨x, hx, hxEq⟩ := hp
  have hpC : projection p ∈ c.chart.source := hxEq ▸ c.chart.symm_mapsTo (hKU hx)
  have hpK : c.chart (projection p) ∈ K := by rwa [← hxEq, c.chart.right_inv (hKU hx)]
  let N := atlasAmplitudeMatrix c A.density p
  have hN : N.PosSemidef := by
    change (atlasAmplitudeMatrix c A.density p).PosSemidef
    rw [atlasAmplitudeMatrix_of_mem c A.density p hpC]
    exact hData.2.1 (chartTangentBasis c (projection p) hpC)
  let G := 16 * (C * ℓ)^2
  have hTrace : (T₁.principal ξ * N * (T₁.principal ξ)ᴴ).trace.re ≤ G * (P * N * Pᴴ).trace.re ∧
      (T₂.principal ξ * N * (T₂.principal ξ)ᴴ).trace.re ≤ G * (P * N * Pᴴ).trace.re := by
    by_cases hNull : hamiltonian B hSig.isNondegenerate p = 0
    · exact hComp x₀ hx₀ p hpC hpK hNull ℓ (hℓ _ hpK) hℓ₁ A.density hData.2.2 hN _ _ hT₁ hT₂
    · have hP : P * N = 0 := projectedAtlasAmplitude_eq_zero_off_null B hSig.isSymmetric
        hSig.isNondegenerate A.density c p hpC hData.2.2 hNull
      have hCol (j : OrderedPair) : P *ᵥ N.col j = 0 := by
        funext a
        exact congrFun (congrFun hP a) j
      have hA₁ : T₁.principal ξ * N = 0 := by
        ext a b
        have ht : tensorOfVector (T₁.principal ξ *ᵥ N.col b) =
            tensorOfVector (P *ᵥ N.col b) - S (tensorOfVector (P *ᵥ N.col b)) q := hT₁ (N.col b)
        rw [show tensorOfVector (P *ᵥ N.col b) = (0 : ComplexTensor2) from congrArg tensorOfVector (hCol b),
          show S 0 q = 0 from complexWideScreen_zero i o m q, sub_zero] at ht
        exact congrFun (congrFun ht a.1) a.2
      have hA₂ : T₂.principal ξ * N = 0 := by
        ext a b
        have ht : tensorOfVector (T₂.principal ξ *ᵥ N.col b) =
            (normalizedFrozenPhase m ξ : ℂ) • S (tensorOfVector (P *ᵥ N.col b)) q := hT₂ (N.col b)
        rw [show tensorOfVector (P *ᵥ N.col b) = (0 : ComplexTensor2) from congrArg tensorOfVector (hCol b),
          show S 0 q = 0 from complexWideScreen_zero i o m q, smul_zero] at ht
        exact congrFun (congrFun ht a.1) a.2
      simp [hP, hA₁, hA₂]
  let v := (chartVolumeDensity B c (fixedChartPhase c p.val).1)⁻¹
  have hv : 0 ≤ v := inv_nonneg.mpr (Real.sqrt_nonneg _)
  let w := ((χ : E → ℝ) (fixedChartPhase c p.val).1)^2 * ‖ξ‖^2
  have hw : 0 ≤ w := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hTest (T : ClassicalMatrixMultiplier OrderedPair) (h :
      (T.principal ξ * N * (T.principal ξ)ᴴ).trace.re ≤ G * (P * N * Pᴴ).trace.re) :
      globalDefectNormIntegrand B c χ T A p ≤ G * W := by
    change w * (T.principal ξ * (v : ℂ) • N * (T.principal ξ)ᴴ).trace.re ≤
      G * (w * (P * (v : ℂ) • N * Pᴴ).trace.re)
    rw [weightedTrace_re, weightedTrace_re]
    have hMul := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hv) hw
    exact hMul.trans_eq (by ring)
  exact ⟨hTest T₁ hTrace.1, hTest T₂ hTrace.2⟩

end Burnett.C02
