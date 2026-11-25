import Burnett.Analysis.Microlocal.Overlap.ReceivingChartCovariantGradient
import Burnett.Analysis.GaugeProjection.ProjectedDefectOriginalGradient
import Burnett.Analysis.GaugeProjection.ProjectedChartRepresentatives
import Burnett.Analysis.GaugeProjection.UniformIntrinsicProjectedSource

/-! Arbitrary chart cutoffs in the original coordinate strong compactness test. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 4200000

noncomputable section
namespace Burnett.P01

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Fourier Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport test_memLp)
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

local notation "E" => CoordinateSpace

omit [SecondCountableTopology M] in
private theorem fixedHalfDensity_pos (B : Field (M := M)) (hn : IsNondegenerate B)
    (c : AtlasChart M) {x : E} (hx : x ∈ c.chart.target) : 0 < fixedHalfDensity B c x :=
  Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr (fixedForm_det_ne_zero B hn c hx)))

/-- Choose the test cutoff whose fixed background half-density produces
the exact original, unweighted coordinate cutoff. -/
def inverseHalfDensityCutoff (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) : D :=
  ⟨fun x => (χ : E → ℝ) x * (fixedHalfDensity B c x)⁻¹,
    ⟨contDiff_test_mul_local c.chart.open_target (test_smooth χ) hχ
      ((fixedHalfDensity_smooth B hB hn c).inv (fun _ hx => (fixedHalfDensity_pos B hn c hx).ne')),
      (test_compactSupport χ).mul_right⟩⟩

theorem inverseHalfDensityCutoff_tsupport (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    tsupport (inverseHalfDensityCutoff B hB hn c χ hχ : E → ℝ) ⊆ tsupport (χ : E → ℝ) :=
  tsupport_mul_subset_left

theorem fixedWeightedCutoff_inverseHalfDensityCutoff
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    fixedWeightedCutoff B hB hn c (inverseHalfDensityCutoff B hB hn c χ hχ)
      ((inverseHalfDensityCutoff_tsupport B hB hn c χ hχ).trans hχ) = χ := by
  apply Subtype.ext
  funext x
  change (χ : E → ℝ) x * (fixedHalfDensity B c x)⁻¹ * fixedHalfDensity B c x = (χ : E → ℝ) x
  by_cases hx : x ∈ tsupport (χ : E → ℝ)
  · rw [mul_assoc, inv_mul_cancel₀ (fixedHalfDensity_pos B hn c (hχ hx)).ne', mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]

open private coordinateDerivative_tsupport_le from Burnett.Analysis.GaugeProjection.UniformIntrinsicProjectedSource

/-- The derivative of the actual zero-extended coordinate fluctuation differs
from the original cutoff gradient by a strongly vanishing whole-space term. -/
theorem exists_receiving_cutoff_metric_and_derivative_error
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hconv : LocallyUniformlyConverges r g B)
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target) :
    ∃ z : ℕ → ProjectionSchwartzMatrix,
      (∀ n x i j, z n i j x = (((χ : E → ℝ) x * fixedPerturbation B (g n) c x i j : ℝ) : ℂ)) ∧
      (∀ i j : Index, Tendsto (fun n => (z n i j).toLp 2 volume) atTop (𝓝 0)) ∧
      ∀ a i j : Index, Tendsto (fun n => (coordinateDerivative a (z n i j)).toLp 2 volume -
        (fixedGradientSchwartz B g hB hg c χ hχ n (a, i, j)).toLp 2 volume) atTop (𝓝 0) := by
  let K := tsupport (χ : E → ℝ)
  let C (H : Field (M := M)) := metricComponents (fixedForm H c)
  have hK : IsCompact K := test_compactSupport χ
  obtain ⟨G, G₀, hG, hG₀, nearG, nearG₀⟩ := exists_openChartMetricRepresentatives hK
    c.chart.open_target hχ (fun n => C (g n)) (C B)
      (fun n => fixedForm_components_smooth (g n) (hg n) c) (fixedForm_components_smooth B hB c)
  have agree n x (hx : x ∈ K) := (nearG n).filter_mono (nhds_le_nhdsSet hx)
  have agree₀ x (hx : x ∈ K) := nearG₀.filter_mono (nhds_le_nhdsSet hx)
  have hConvG : TendstoUniformlyOn G G₀ atTop K :=
    ((fixed_components_uniform_of_physical_C0loc r g B hconv c K hK hχ).congr
      (Eventually.of_forall fun n x hx => (agree n x hx).eq_of_nhds.symm)).congr_right
      (fun x hx => (agree₀ x hx).eq_of_nhds.symm)
  obtain ⟨η, hη, hηc, _, V, _, hKV, _, hηV⟩ := exists_projectedChartCutoff hK c.chart.open_target hχ
  let d : D := ⟨η, hη, hηc⟩
  have hd (x : E) (hx : x ∈ K) : (d : E → ℝ) x = 1 := hηV (hKV hx)
  let z n := localizedMetricSchwartz (G n) G₀ χ (test_smooth χ) hK (hG n) hG₀
  have hz (n : ℕ) (x : E) (i j : Index) :
      z n i j x = (((χ : E → ℝ) x * fixedPerturbation B (g n) c x i j : ℝ) : ℂ) := by
    change (((χ : E → ℝ) x * (G n x i j - G₀ x i j) : ℝ) : ℂ) = _
    by_cases hx : x ∈ K
    · rw [(agree n x hx).eq_of_nhds, (agree₀ x hx).eq_of_nhds]
      rfl
    · rw [image_eq_zero_of_notMem_tsupport hx, zero_mul, zero_mul]
  refine ⟨z, hz, ?_, ?_⟩
  · intro i j
    apply tendsto_weighted_localizationError_L2_zero K χ (test_memLp χ)
      (fun _ hx => image_eq_zero_of_notMem_tsupport hx) (fun n => fixedComponent B g c n (i, j))
      (fixedComponent_localUniform r B g hconv c (i, j) K hK hχ)
    intro n
    filter_upwards [(z n i j).coeFn_toLp 2 volume] with x hx
    exact hx.trans (hz n x i j)
  · intro a i j
    let W n := (fixedGradientSchwartz B g hB hg c χ hχ n (a, i, j)).toLp 2 volume
    have hDeriv n : symbolCLM (physicalCoefficient d) ((coordinateDerivative a (z n i j)).toLp 2 volume) =
        (coordinateDerivative a (z n i j)).toLp 2 volume := by
      apply Lp.ext
      let f := coordinateDerivative a (z n i j)
      filter_upwards [symbolL2_ae (physicalCoefficient d) (f.toLp 2 volume), f.coeFn_toLp 2 volume] with x hx he
      change symbolL2 (physicalCoefficient d) (f.toLp 2 volume) x = _
      rw [hx, he]
      change (d.val x : ℂ) * f x = f x
      by_cases hs : x ∈ K
      · rw [hd x hs, Complex.ofReal_one, one_mul]
      · have hf : x ∉ tsupport (f : E → ℂ) := fun hx => hs
          ((coordinateDerivative_tsupport_le _ _).trans
            (localizedMetricSchwartz_tsupport_subset (G n) G₀ χ (test_smooth χ) hK (hG n) hG₀ i j) hx)
        rw [image_eq_zero_of_notMem_tsupport hf, mul_zero]
    have hW (n : ℕ) : (W n : E → ℂ) =ᵐ[volume] fun x =>
        ((d : E → ℝ) x * (χ : E → ℝ) x * (coordinateJet (G n) x a i j - coordinateJet G₀ x a i j) : ℝ) := by
      filter_upwards [(fixedGradientSchwartz B g hB hg c χ hχ n (a, i, j)).coeFn_toLp 2 volume] with x hx
      rw [show W n x = _ from hx, fixedGradientSchwartz_apply]
      by_cases hxK : x ∈ K
      · have he := congrFun (congrFun (congrFun (projectedChart_coordinateJet_eq_of_eventuallyEq
          ((agree n x hxK).sub (agree₀ x hxK))) a) i) j
        have hsub : coordinateJet (fun y => G n y - G₀ y) x a i j =
            coordinateJet (G n) x a i j - coordinateJet G₀ x a i j := by
          simp only [coordinateJet, Pi.sub_apply,
            fderiv_fun_sub ((hG n i j).differentiable (by simp) x) ((hG₀ i j).differentiable (by simp) x),
            ContinuousLinearMap.sub_apply]
        change coordinateJet (fun y => G n y - G₀ y) x a i j =
          coordinateJet (fixedPerturbation B (g n) c) x a i j at he
        rw [← he, hsub, hd x hxK, one_mul]
      · rw [image_eq_zero_of_notMem_tsupport hxK, zero_mul, mul_zero, zero_mul]
    have hLim := localizedMetric_weighted_derivative_sub_original_tendsto_zero G G₀ χ (test_smooth χ) hK
      hG hG₀ hConvG d (physicalCoefficient d) (fun _ => rfl) i j a W hW
    change Tendsto (fun n => symbolCLM (physicalCoefficient d) ((coordinateDerivative a (z n i j)).toLp 2 volume) -
      W n) atTop (𝓝 0) at hLim
    simpa only [hDeriv] using hLim

end Burnett.P01
