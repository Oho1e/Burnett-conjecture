import Burnett.Analysis.TransportPatches.WideCompatibleWindow
import Burnett.Analysis.TransportPatches.WideBaselineL2
import Burnett.Analysis.TransportPatches.ReceivingPatchGradientVolume

/-! The actual wide errors have uniform whole-space L² slope on a compact convex window. -/

set_option autoImplicit false
set_option maxRecDepth 5200
set_option maxHeartbeats 5300000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol Burnett.V06 Burnett.Fourier
open Burnett.A02.FrequencySplit (E)
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair tensorOfVector)
open Burnett.F07.IntrinsicAmplitudeCoordinates (chartTangentBasis)
open Burnett.P01 (principalGaugeProjection principalGaugeProjectionMatrix
  tensorOfVector_principalGaugeProjectionMatrix receivingCutoffFluctuation)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff ComplexConjugate ComplexOrder ENNReal Manifold Matrix MatrixOrder Topology

open private norm_tensorOfVector from Burnett.Analysis.TransportPatches.FrozenErrorCompression
open private complexWideScreen_zero weightedTrace_re from Burnett.Analysis.TransportPatches.OriginalWeightedFrozenCompression

local notation "OrderedVector" => OrderedPair → ℂ

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

def orderedGradientL2Norm (T : ClassicalMatrixMultiplier OrderedPair)
    (z : Burnett.P01.ProjectionSchwartzMatrix) : ℝ :=
  ‖WithLp.toLp 2 (fun a : Index × OrderedPair => multiplierCoordinateDerivative T z a.1 a.2)‖

/-- Both actual wide errors use a single choice of cutoffs on the compact
convex chart window. Their exact whole-space L² limits have a uniform
linear slope on every sufficiently small subpatch of that window. -/
theorem exists_actualWideL2_convexWindow
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ (i o L C η : ℝ) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      0 < i ∧ i < o ∧ 0 ≤ L ∧ 0 ≤ C ∧ 0 < η ∧
      ∀ (P : Set E) (hPK : P ⊆ K), IsCompact P →
      ∀ (x₀ : E) (hx₀ : x₀ ∈ P) (d : ℝ), (∀ x ∈ P, ‖x - x₀‖ ≤ d) → d ≤ 1 → L * d ≤ η →
      ∀ (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ P),
        let m := chartInverseMetric B c x₀
        let hm := hf x₀ (hPK hx₀)
        let T₁ := actualFrozenScreenErrorMultiplier i o m hm
        let T₂ := actualFrozenPhaseErrorMultiplier i o m hm
        let T₀ := originalProjectedMatrixMultiplier
        let z := receivingCutoffFluctuation B g hB hg c χ (hχ.trans (hPK.trans hKU))
        let τ := A.control.restrict (amplitudeCosphereWindow r (c.chart.symm '' P))
        let H (T : ClassicalMatrixMultiplier OrderedPair) := globalDefectNormIntegrand B c χ T A
        let N (T : ClassicalMatrixMultiplier OrderedPair) := Real.sqrt (∫ p, H T p ∂τ)
        Tendsto (fun n => orderedGradientL2Norm T₀ (z (σ n))) atTop (𝓝 (N T₀)) ∧
        Tendsto (fun n => orderedGradientL2Norm T₁ (z (σ n))) atTop (𝓝 (N T₁)) ∧
        Tendsto (fun n => orderedGradientL2Norm T₂ (z (σ n))) atTop (𝓝 (N T₂)) ∧
        N T₁ ≤ 4 * C * d * N T₀ ∧ N T₂ ≤ 4 * C * d * N T₀ := by
  obtain ⟨i, o, L, C, η, hi, hio, hL, hC, hη, hf, hKernel⟩ :=
    exists_compatibleWideWindow (r := r) B hB hSig c K hK hConv hKU
  refine ⟨i, o, L, C, η, hf, hi, hio, hL, hC, hη, ?_⟩
  intro P hPK hP x₀ hx₀ d hd hd₁ hSmall χ hχ m hm T₁ T₂ T₀ z τ H N
  have hComp : ∀ᵐ p ∂τ, H T₁ p ≤ (16 * (C * d)^2) * H T₀ p ∧
      H T₂ p ≤ (16 * (C * d)^2) * H T₀ p := by
    have hPU := hPK.trans hKU
    have hImage : IsCompact (c.chart.symm '' P) := hP.image_of_continuousOn (c.chart.continuousOn_symm.mono hPU)
    have hWindow := measurableSet_amplitudeCosphereWindow r hImage.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hWindow, ae_restrict_of_ae hA.2.2.2.2.2] with p hp hData
    change projection p ∈ c.chart.symm '' P at hp
    obtain ⟨x, hx, hxEq⟩ := hp
    have hpC : projection p ∈ c.chart.source := hxEq ▸ c.chart.symm_mapsTo (hPU hx)
    have hpP : c.chart (projection p) ∈ P := by rwa [← hxEq, c.chart.right_inv (hPU hx)]
    let q := atlasChartUnitCovector c p
    let ξ : E := WithLp.toLp 2 q
    let N := atlasAmplitudeMatrix c A.density p
    let Q := principalGaugeProjectionMatrix ξ
    have hN : N.PosSemidef := by
      change (atlasAmplitudeMatrix c A.density p).PosSemidef
      rw [atlasAmplitudeMatrix_of_mem c A.density p hpC]
      exact hData.2.1 (chartTangentBasis c (projection p) hpC)
    have hScale : 0 ≤ C * d := mul_nonneg hC ((norm_nonneg _).trans (hd x₀ hx₀))
    have hRange (v : OrderedVector) (hv : v ∈ LinearMap.range N.mulVecLin) :
        ‖T₁.principal ξ *ᵥ v‖ ≤ (C * d) * ‖Q *ᵥ v‖ ∧
        ‖T₂.principal ξ *ᵥ v‖ ≤ (C * d) * ‖Q *ᵥ v‖ := by
      obtain ⟨w, rfl⟩ := hv
      let u : OrderedVector := N *ᵥ w
      let J := tensorOfVector (Q *ᵥ u)
      let S := complexWideScreen i o m J q
      have hOut₁ : tensorOfVector (T₁.principal ξ *ᵥ u) = J - S := by
        change tensorOfVector ((actualFrozenScreenErrorMultiplier i o m hm).principal ξ *ᵥ u) = _
        rw [actualFrozenScreenErrorMultiplier_principal]
        exact tensorOfVector_actualFrozenScreenErrorOrdered i o m ξ u
      have hOut₂ : tensorOfVector (T₂.principal ξ *ᵥ u) = (normalizedFrozenPhase m ξ : ℂ) • S := by
        change tensorOfVector ((actualFrozenPhaseErrorMultiplier i o m hm).principal ξ *ᵥ u) = _
        rw [actualFrozenPhaseErrorMultiplier_principal]
        exact tensorOfVector_actualFrozenPhaseErrorOrdered i o m ξ u
      change ‖T₁.principal ξ *ᵥ u‖ ≤ _ * ‖Q *ᵥ u‖ ∧ ‖T₂.principal ξ *ᵥ u‖ ≤ _ * ‖Q *ᵥ u‖
      rw [← norm_tensorOfVector (T₁.principal ξ *ᵥ u), ← norm_tensorOfVector (T₂.principal ξ *ᵥ u),
        ← norm_tensorOfVector (Q *ᵥ u), hOut₁, hOut₂]
      by_cases hNull : hamiltonian B hSig.isNondegenerate p = 0
      · obtain ⟨hSym, hR⟩ := P01.atlasAmplitudeMatrix_receiving_ricciKernel B c
          hSig.isSymmetric hSig.isNondegenerate A.density p hpC hData.2.2 w
        have hJ := tensorOfVector_principalGaugeProjectionMatrix ξ u
        change J = principalGaugeProjection ξ (tensorOfVector u) at hJ
        have hh := hKernel x₀ (hPK hx₀) p hpC (hPK hpP) hNull d (hd _ hpP) hd₁ hSmall
          (tensorOfVector u) hSym hR
        let J₀ : ComplexTensor2 := principalGaugeProjection ξ (tensorOfVector u)
        change ‖J₀ - complexWideScreen i o m J₀ q‖ ≤ C * d * ‖J₀‖ ∧
          ‖(normalizedFrozenPhase m ξ : ℂ) • complexWideScreen i o m J₀ q‖ ≤ C * d * ‖J₀‖ at hh
        change J = J₀ at hJ
        rw [← hJ] at hh
        exact hh
      · have hQ : Q * N = 0 := projectedAtlasAmplitude_eq_zero_off_null B hSig.isSymmetric
          hSig.isNondegenerate A.density c p hpC hData.2.2 hNull
        have hJ : J = 0 := by
          calc
            J = tensorOfVector (Q *ᵥ (N *ᵥ w)) := rfl
            _ = tensorOfVector (0 : OrderedVector) := by rw [Matrix.mulVec_mulVec, hQ, Matrix.zero_mulVec]
            _ = 0 := rfl
        have hS : S = 0 := by
          change complexWideScreen i o m J q = 0
          rw [hJ, complexWideScreen_zero]
        simp [hJ, hS]
        exact mul_nonneg hScale (norm_nonneg _)
    let C' := 16 * (C * d)^2
    have hWeight (T : ClassicalMatrixMultiplier OrderedPair) (h :
        (T.principal ξ * N * (T.principal ξ)ᴴ).trace.re ≤ C' * (Q * N * Qᴴ).trace.re) :
        globalDefectNormIntegrand B c χ T A p ≤ C' * globalDefectNormIntegrand B c χ T₀ A p := by
      let v := (chartVolumeDensity B c (fixedChartPhase c p.val).1)⁻¹
      have hv : 0 ≤ v := inv_nonneg.mpr (Real.sqrt_nonneg _)
      let w := ((χ : E → ℝ) (fixedChartPhase c p.val).1)^2 * ‖ξ‖^2
      have hw : 0 ≤ w := mul_nonneg (sq_nonneg _) (sq_nonneg _)
      change w * (T.principal ξ * (v : ℂ) • N * (T.principal ξ)ᴴ).trace.re ≤
        C' * (w * (originalProjectedMatrixMultiplier.principal ξ * (v : ℂ) • N *
          (originalProjectedMatrixMultiplier.principal ξ)ᴴ).trace.re)
      rw [originalProjectedMatrixMultiplier_principal, weightedTrace_re, weightedTrace_re]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h hv) hw).trans_eq (by ring)
    exact ⟨hWeight T₁ (traceCompression_le_of_range N Q _ hN _ hScale (fun v hv => (hRange v hv).1)),
      hWeight T₂ (traceCompression_le_of_range N Q _ hN _ hScale (fun v hv => (hRange v hv).2))⟩

  let P₀ := c.chart.symm '' P
  have hPU := hPK.trans hKU
  have hP₀ : IsCompact P₀ := hP.image_of_continuousOn (c.chart.continuousOn_symm.mono hPU)
  have hP₀c : P₀ ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm.mapsTo.mono_left hPU)
  have hχP₀ : tsupport (χ : E → ℝ) ⊆ c.chart '' P₀ := by
    intro x hx
    exact ⟨c.chart.symm x, ⟨x, hχ hx, rfl⟩, c.chart.right_inv (hPU (hχ hx))⟩
  have hNorm (T : ClassicalMatrixMultiplier OrderedPair) : Integrable (H T) τ ∧
      Tendsto (fun n => orderedGradientL2Norm T (z (σ n)) ^ 2) atTop (𝓝 (∫ p, H T p ∂τ)) := by
    simpa only [orderedGradientL2Norm, multiplierCoordinateDerivative_norm_sq] using
      tendsto_originalGlobalDefectNorm r B g hB hg hSig.isNondegenerate hconv σ hσ A hPair
        c P₀ hP₀ hP₀c χ hχP₀ T
  have hLim (T : ClassicalMatrixMultiplier OrderedPair) :
      Tendsto (fun n => orderedGradientL2Norm T (z (σ n))) atTop (𝓝 (N T)) := by
    simpa only [N, Function.comp_def, orderedGradientL2Norm, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto (∫ p, H T p ∂τ)).comp (hNorm T).2
  let C' := 16 * (C * d)^2
  have hd₀ : 0 ≤ d := (norm_nonneg _).trans (hd x₀ hx₀)
  have hCroot : Real.sqrt C' = 4 * C * d := by
    rw [show C' = (4 * C * d)^2 by dsimp [C']; ring,
      Real.sqrt_sq (mul_nonneg (mul_nonneg (by norm_num) hC) hd₀)]
  have hBound (T : ClassicalMatrixMultiplier OrderedPair) (h : ∀ᵐ p ∂τ, H T p ≤ C' * H T₀ p) :
      N T ≤ 4 * C * d * N T₀ := by
    have hI := integral_mono_ae (hNorm T).1 ((hNorm T₀).1.const_mul C') h
    rw [integral_const_mul] at hI
    have hh := Real.sqrt_le_sqrt hI
    rw [Real.sqrt_mul (by dsimp [C']; positivity), hCroot] at hh
    exact hh
  exact ⟨hLim T₀, hLim T₁, hLim T₂, hBound T₁ (hComp.mono (fun _ h => h.1)),
    hBound T₂ (hComp.mono (fun _ h => h.2))⟩

/-- The C01 derivative-volume estimate on the same patch gives both
whole-space wide errors the rate radius times the square root of the
patch's Lebesgue volume, with a uniform window constant. -/
theorem exists_actualWideL2_convexWindow_volume
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hSig : HasLorentzSignature B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target)
    (Craw : ℝ) (hRawC : 0 ≤ Craw) :
    ∃ (i o L C₂ η : ℝ) (hf : ∀ x ∈ K, WideScreenFrequencySmooth i o (chartInverseMetric B c x)),
      0 < i ∧ i < o ∧ 0 ≤ L ∧ 0 ≤ C₂ ∧ 0 < η ∧
      ∀ (P : Set E) (hPK : P ⊆ K), IsCompact P →
      ∀ (x₀ : E) (hx₀ : x₀ ∈ P) (d : ℝ), (∀ x ∈ P, ‖x - x₀‖ ≤ d) → d ≤ 1 → L * d ≤ η →
      ∀ (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ P),
        (∀ᶠ n in atTop, eLpNorm (fderiv ℝ (receivingRealPatchField B (g n) c χ)) 2 volume ≤
          ENNReal.ofReal Craw * (volume : Measure E) P ^ (1 / 2 : ℝ)) →
        let m := chartInverseMetric B c x₀
        let hm := hf x₀ (hPK hx₀)
        let T₁ := actualFrozenScreenErrorMultiplier i o m hm
        let T₂ := actualFrozenPhaseErrorMultiplier i o m hm
        let z := receivingCutoffFluctuation B g hB hg c χ (hχ.trans (hPK.trans hKU))
        let R := C₂ * d * ((volume : Measure E) P).toReal ^ (1 / 2 : ℝ)
        ∀ ε > 0, ∀ᶠ n in atTop, orderedGradientL2Norm T₁ (z (σ n)) ≤ R + ε ∧
          orderedGradientL2Norm T₂ (z (σ n)) ≤ R + ε := by
  obtain ⟨i, o, L, C, η, hf, hi, hio, hL, hC, hη, hL2⟩ :=
    exists_actualWideL2_convexWindow r B g hB hg hSig hconv σ hσ A hA hPair c K hK hConv hKU
  obtain ⟨B₀, hB₀, hProject⟩ := exists_originalProjectedMatrixMultiplier_L2_volume
  let C₂ := 4 * C * B₀ * Craw
  have hC₂ : 0 ≤ C₂ := mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC) hB₀) hRawC
  refine ⟨i, o, L, C₂, η, hf, hi, hio, hL, hC₂, hη, ?_⟩
  intro P hPK hP x₀ hx₀ d hd hd₁ hSmall χ hχ hRaw m hm T₁ T₂ z R ε hε
  have hVol := receivingCutoffFluctuation_eventually_derivative_volume B g hB hg c χ
    (hχ.trans (hPK.trans hKU)) σ hσ P 2 Craw
    (by simpa only [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num] using hRaw)
  have hBase := hProject (fun n => z (σ n)) P Craw hP hRawC hVol
  obtain ⟨h₀, h₁, h₂, hSlope₁, hSlope₂⟩ := hL2 P hPK hP x₀ hx₀ d hd hd₁ hSmall χ hχ
  let v := ((volume : Measure E) P).toReal ^ (1 / 2 : ℝ)
  have hLim₀ := le_of_tendsto h₀ hBase
  have hNonneg : 0 ≤ 4 * C * d := mul_nonneg (mul_nonneg (by norm_num) hC) ((norm_nonneg _).trans (hd x₀ hx₀))
  have hBound : 4 * C * d * (B₀ * Craw * v) = C₂ * d * v := by dsimp only [C₂]; ring
  have hFin₁ := hSlope₁.trans ((mul_le_mul_of_nonneg_left hLim₀ hNonneg).trans_eq hBound)
  have hFin₂ := hSlope₂.trans ((mul_le_mul_of_nonneg_left hLim₀ hNonneg).trans_eq hBound)
  filter_upwards [h₁.eventually (Iio_mem_nhds (hFin₁.trans_lt (lt_add_of_pos_right _ hε))),
    h₂.eventually (Iio_mem_nhds (hFin₂.trans_lt (lt_add_of_pos_right _ hε)))] with n hn₁ hn₂
  exact ⟨hn₁.le, hn₂.le⟩

end Burnett.C02
