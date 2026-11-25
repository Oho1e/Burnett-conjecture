import Burnett.Analysis.TransportPatches.ActualThinConeL2
import Burnett.Analysis.TransportPatches.WideCompatibleWindowNorm

/-! The exact thin complement has zero defect on each sufficiently small subpatch of one mother window. -/
set_option autoImplicit false
set_option maxRecDepth 5100
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.A02.FrequencySplit (E)
open Burnett.Geometry.UnitCosphere (Cosphere hamiltonian projection)
open Burnett.Microlocal.Overlap
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (receivingCutoffFluctuation)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Matrix Topology

variable {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The same projected covariance gives the strong-zero actual complement.
The metric Lipschitz constant comes from the fixed convex mother window. -/
theorem exists_thinComplement_subpatch_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hA : HasOriginalIntrinsicAmplitude r B g hB hg hn σ A)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (K : Set E) (hK : IsCompact K) (hConv : Convex ℝ K) (hKU : K ⊆ c.chart.target) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (P : Set E) (hPK : P ⊆ K), IsCompact P →
      ∀ x₀ ∈ P, ∀ d : ℝ, (∀ x ∈ P, ‖x - x₀‖ ≤ d) →
      ∀ (η inner outer : ℝ) (hη : 0 < η), 0 ≤ inner → inner < outer → L * d ≤ inner * η →
      ∀ (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ P),
      let z := receivingCutoffFluctuation B g hB hg c χ (hχ.trans (hPK.trans hKU))
      let T := actualThinConeComplementMultiplier (chartInverseMetric B c x₀) hη inner outer
      Tendsto (fun n => WithLp.toLp 2 (fun a : Index × OrderedPair =>
        multiplierCoordinateDerivative T (z (σ n)) a.1 a.2)) atTop (𝓝 0) := by
  obtain ⟨L, hL, hPhase⟩ := exists_actualNull_frozenPhaseAndThinCone (r := r) B hB hs hn c K hK hConv hKU
  refine ⟨L, hL, ?_⟩
  intro P hPK hP x₀ hx₀ d hd η inner outer hη hInner hIO hSmall χ hχ z T
  have hPU := hPK.trans hKU
  let P₀ := c.chart.symm '' P
  have hP₀ : IsCompact P₀ := hP.image_of_continuousOn (c.chart.continuousOn_symm.mono hPU)
  have hP₀c : P₀ ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm.mapsTo.mono_left hPU)
  have hχ₀ : tsupport (χ : E → ℝ) ⊆ c.chart '' P₀ := by
    intro x hx
    exact ⟨c.chart.symm x, ⟨x, hχ hx, rfl⟩, c.chart.right_inv (hPU (hχ hx))⟩
  let τ := A.control.restrict (amplitudeCosphereWindow r P₀)
  let H := globalDefectNormIntegrand B c χ T A
  have hLim : Tendsto (fun n => ∑ b : Index, ∑ k : OrderedPair,
      ‖multiplierCoordinateDerivative T (z (σ n)) b k‖^2) atTop (𝓝 (∫ p, H p ∂τ)) :=
    (tendsto_originalGlobalDefectNorm r B g hB hg hn hconv σ hσ A hPair c P₀ hP₀ hP₀c χ hχ₀ T).2
  have hZero : H =ᵐ[τ] 0 := by
    have hWin := measurableSet_amplitudeCosphereWindow r hP₀.isClosed.measurableSet
    filter_upwards [ae_restrict_mem (μ := A.control) hWin, ae_restrict_of_ae hA.2.2.2.2.2] with p hp hData
    change projection p ∈ P₀ at hp
    obtain ⟨x, hx, he⟩ := hp
    have hpC : projection p ∈ c.chart.source := he ▸ c.chart.symm_mapsTo (hPU hx)
    have hpP : c.chart (projection p) ∈ P := by rwa [← he, c.chart.right_inv (hPU hx)]
    let ξ : E := WithLp.toLp 2 (atlasChartUnitCovector c p)
    have hAnn : T.principal ξ * atlasAmplitudeMatrix c A.density p = 0 := by
      change thinConeComplementMatrix (chartInverseMetric B c x₀) η inner outer ξ *
        atlasAmplitudeMatrix c A.density p = 0
      by_cases hNull : hamiltonian B hn p = 0
      · have hOne := (hPhase x₀ (hPK hx₀) p hpC (hPK hpP) hNull d (hd _ hpP)).2
          η inner outer hη hInner hIO hSmall
        change Burnett.Analysis.ProjectiveNullCaps.thinConeProfile (chartInverseMetric B c x₀) η inner outer ξ = 1 at hOne
        simp [thinConeComplementMatrix, hOne]
      · rw [thinConeComplementMatrix, smul_mul_assoc,
          projectedAtlasAmplitude_eq_zero_off_null B hs hn A.density c p hpC hData.2.2 hNull, smul_zero]
    have hProd : T.principal ξ * chartLebesgueAmplitude B c A p = 0 := by
      simp only [chartLebesgueAmplitude, Matrix.mul_smul, hAnn, smul_zero]
    change ((χ : E → ℝ) (Geometry.FixedCotangentChart.fixedChartPhase c p.val).1)^2 *
      ‖ξ‖^2 * (T.principal ξ * chartLebesgueAmplitude B c A p * (T.principal ξ)ᴴ).trace.re = 0
    simp [hProd]
  have hIeq := integral_congr_ae hZero
  simp only [Pi.zero_apply, integral_zero] at hIeq
  rw [hIeq] at hLim
  have hSq : Tendsto (fun n => orderedGradientL2Norm T (z (σ n)) ^ 2) atTop (𝓝 0) := by
    simpa only [orderedGradientL2Norm, multiplierCoordinateDerivative_norm_sq] using hLim
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hRoot := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hSq
  simpa only [Function.comp_def, orderedGradientL2Norm, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hRoot

end Burnett.C02
