import Burnett.Analysis.TransportPatches.OriginalGlobalDefectNorm

/-! The exact whole-cosphere formula for an arbitrary chart-supported real cutoff. -/

set_option autoImplicit false
set_option maxRecDepth 5000
set_option maxHeartbeats 6200000

noncomputable section

namespace Burnett.C02

open Set Filter Function MeasureTheory Matrix Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.Overlap
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.Geometry.FixedCotangentChart (fixedChartPhase fixedChartPhase_of_mem)
open Burnett.RicciSymbol (Index)
open Burnett.X02.SobolevTestJet (D test_compactSupport)
open Burnett.P01 (receivingCutoffFluctuation)
open scoped BigOperators ComplexConjugate ContDiff Manifold Matrix Topology

local notation "E" => CoordinateSpace

variable {M J : Type*} [Fintype J] [TopologicalSpace M] [T2Space M] [ChartedSpace E M]
  [IsManifold Model ∞ M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The original ordered amplitude test, reweighted to chart Lebesgue volume. -/
def globalDefectNormIntegrand {r : Metric (M := M)} (B : Field (M := M)) (c : AtlasChart M)
    (χ : D) (T : ClassicalMatrixMultiplier J) (A : IntrinsicAmplitudeCovariance r) (p : Cosphere r) : ℝ :=
  let x := (fixedChartPhase c p.val).1
  let ξ : E := WithLp.toLp 2 (atlasChartUnitCovector c p)
  let P := T.principal ξ
  ((χ : E → ℝ) x)^2 * ‖ξ‖^2 * (P * chartLebesgueAmplitude B c A p * Pᴴ).trace.re

/-- The left side is a full coordinate-space L² energy. The right side is
an integral on the full original cosphere, supported over the cutoff chart. -/
theorem tendsto_originalGlobalDefectNorm_wholeCosphere
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r)
    (hPair : HasOriginalReceivingLocalClassicalPairings r B g hB hg hn σ A)
    (c : AtlasChart M) (χ : D) (hχc : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (T : ClassicalMatrixMultiplier J) :
    let z := receivingCutoffFluctuation B g hB hg c χ hχc
    let H := globalDefectNormIntegrand B c χ T A
    Integrable H A.control ∧
    Tendsto (fun n =>
      ‖WithLp.toLp 2 (fun a : Index × J => multiplierCoordinateDerivative T (z (σ n)) a.1 a.2)‖^2)
      atTop (𝓝 (∫ p, H p ∂A.control)) := by
  intro z H
  let K := c.chart.symm '' tsupport (χ : E → ℝ)
  have hK : IsCompact K :=
    (test_compactSupport χ).image_of_continuousOn (c.chart.continuousOn_symm.mono hχc)
  have hKc : K ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm.mapsTo.mono_left hχc)
  have hχ : tsupport (χ : E → ℝ) ⊆ c.chart '' K := by
    intro x hx
    exact ⟨c.chart.symm x, ⟨x, hx, rfl⟩, c.chart.right_inv (hχc hx)⟩
  obtain ⟨hI, hLim⟩ := tendsto_originalGlobalDefectNorm r B g hB hg hn hconv σ hσ A hPair
    c K hK hKc χ hχ T
  let S := amplitudeCosphereWindow r K
  have hS : MeasurableSet S := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hZero (p : Cosphere r) (hp : p ∉ S) : H p = 0 := by
    by_cases hc : projection p ∈ c.chart.source
    · have hPhase : (fixedChartPhase c p.val).1 = c.chart (projection p) := by
        exact congrArg Prod.fst (fixedChartPhase_of_mem c p.val hc)
      have hx : (fixedChartPhase c p.val).1 ∉ tsupport (χ : E → ℝ) := by
        intro hz
        rw [hPhase] at hz
        apply hp
        change projection p ∈ K
        exact ⟨c.chart (projection p), hz, c.chart.left_inv hc⟩
      have hχzero := image_eq_zero_of_notMem_tsupport (f := (χ : E → ℝ)) hx
      norm_num [H, globalDefectNormIntegrand, hχzero]
    · have hc' : p.val.proj ∉ c.chart.source := hc
      have hξ : atlasChartUnitCovector c p = 0 := by
        simp [atlasChartUnitCovector, fixedChartPhase, hc']
      simp [H, globalDefectNormIntegrand, hξ]
  have hInd : S.indicator H = H := by
    funext p
    by_cases hp : p ∈ S
    · exact indicator_of_mem hp _
    · rw [indicator_of_notMem hp, hZero p hp]
  have hI' : Integrable (S.indicator H) A.control := (integrable_indicator_iff hS).mpr hI
  have hInt : (∫ p, H p ∂A.control) = ∫ p in S, H p ∂A.control := by
    calc
      _ = ∫ p, S.indicator H p ∂A.control := by rw [hInd]
      _ = _ := integral_indicator hS
  refine ⟨hInd ▸ hI', ?_⟩
  simpa only [multiplierCoordinateDerivative_norm_sq, hInt] using hLim

end Burnett.C02
