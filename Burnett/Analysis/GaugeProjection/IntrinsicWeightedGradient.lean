import Burnett.Analysis.GaugeProjection.ProjectedDefectOriginalGradient
import Burnett.Analysis.GaugeProjection.ProjectedChartRepresentatives
import Burnett.Analysis.Microlocal.OriginalCoordinateCurl
import Burnett.Analysis.Microlocal.Overlap.HalfDensity

set_option autoImplicit false
noncomputable section

namespace Burnett.P01

open Set Filter MeasureTheory Burnett.RicciSymbol Burnett.Fourier Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricSequence
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.F05.OriginalCoordinateCurl Burnett.F05.ChartVolumeBridge
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff Topology Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Instantiate the raw-jet witness with the whole-space F05 Lebesgue input,
using the physical metric sequence and a single chosen surface weight and field. -/
theorem exists_intrinsic_originalGradient_halfDensity_error_tendsto_zero
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (hconv : LocallyUniformlyConverges r g B)
    (c : M) (χ : D) (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartAt CoordinateSpace c).target) :
    let ψ := chartVolumeWeightedCutoff B hB hn c χ hχ
    let hψ := (chartVolumeWeightedCutoff_tsupport B hB hn c χ hχ).trans hχ
    ∃ (d : D) (z : ℕ → ProjectionSchwartzMatrix),
      EqOn (d : CoordinateSpace → ℝ) (chartHalfDensity B c) (tsupport (χ : CoordinateSpace → ℝ)) ∧
      (∀ n x i j, z n i j x = (((χ : CoordinateSpace → ℝ) x *
        (metricComponents (coordinateBilinear (g n) c) x i j -
          metricComponents (coordinateBilinear B c) x i j) : ℝ) : ℂ)) ∧
      ∀ a i j : Index, Tendsto (fun n => symbolCLM (physicalCoefficient d)
        ((coordinateDerivative a (z n i j)).toLp 2 volume) -
        (originalGradientSchwartz B g hB hg c ψ hψ n (a,i,j)).toLp 2 volume) atTop (𝓝 0) := by
  intro ψ hψ
  let K := tsupport (χ : CoordinateSpace → ℝ)
  have hK : IsCompact K := test_compactSupport χ
  obtain ⟨G, G₀, hG, hG₀, nearG, nearG₀⟩ :=
    exists_openChartMetricRepresentatives hK (chartAt CoordinateSpace c).open_target hχ
      (fun n => metricComponents (coordinateBilinear (g n) c)) (metricComponents (coordinateBilinear B c))
      (fun n => contDiffOn_metricComponents (g n) (hg n) c) (contDiffOn_metricComponents B hB c)
  have agree (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) :=
    (nearG n).filter_mono (nhds_le_nhdsSet hx)
  have agree₀ (x : CoordinateSpace) (hx : x ∈ K) :=
    nearG₀.filter_mono (nhds_le_nhdsSet hx)
  have hConvG : TendstoUniformlyOn G G₀ atTop K :=
    ((components_uniform_of_physical_C0loc r g B hconv c K hK hχ).congr
      (Eventually.of_forall fun n x hx => (agree n x hx).eq_of_nhds.symm)).congr_right
      (fun x hx => (agree₀ x hx).eq_of_nhds.symm)
  obtain ⟨η, hη, hηc, hηU, V, _, hKV, _, hηV⟩ :=
    exists_projectedChartCutoff hK (chartAt CoordinateSpace c).open_target hχ
  let θ : D := ⟨η, hη, hηc⟩
  let d := chartVolumeWeightedCutoff B hB hn c θ hηU
  have hd : EqOn (d : CoordinateSpace → ℝ) (chartHalfDensity B c) K := by
    intro x hx
    change η x * chartHalfDensity B c x = _
    simp only [hηV (hKV hx), Pi.one_apply, one_mul]
  let z n := localizedMetricSchwartz (G n) G₀ χ (test_smooth χ) hK (hG n) hG₀
  refine ⟨d, z, hd, ?_, ?_⟩
  · intro n x i j
    change (((χ : CoordinateSpace → ℝ) x * (G n x i j - G₀ x i j) : ℝ) : ℂ) = _
    by_cases hx : x ∈ K
    · rw [(agree n x hx).eq_of_nhds, (agree₀ x hx).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · intro a i j
    apply localizedMetric_weighted_derivative_sub_original_tendsto_zero G G₀ χ (test_smooth χ) hK
      hG hG₀ hConvG d (physicalCoefficient d) (fun _ => rfl) i j a
    intro n
    let w := originalGradientSchwartz B g hB hg c ψ hψ n (a,i,j)
    filter_upwards [w.coeFn_toLp 2 volume] with x hx
    rw [hx]
    change originalGradientSchwartz B g hB hg c ψ hψ n (a,i,j) x = _
    rw [originalGradientSchwartz_apply_rawJet]
    simp only [ψ, chartVolumeWeightedCutoff_apply]
    by_cases hxK : x ∈ K
    · have hJ := projectedChart_coordinateJet_eq_of_eventuallyEq ((agree n x hxK).sub (agree₀ x hxK))
      have he := congrFun (congrFun (congrFun hJ a) i) j
      have hD : coordinateJet (fun y => G n y - G₀ y) x a i j =
          coordinateJet (G n) x a i j - coordinateJet G₀ x a i j := by
        simp only [coordinateJet, Pi.sub_apply,
          fderiv_fun_sub ((hG n i j).differentiable (by simp) x) ((hG₀ i j).differentiable (by simp) x),
          ContinuousLinearMap.sub_apply]
      change coordinateJet (fun y => G n y - G₀ y) x a i j =
        coordinateJet (fun y => metricComponents (coordinateBilinear (g n) c) y -
          metricComponents (coordinateBilinear B c) y) x a i j at he
      rw [← he, hD, hd hxK]
      push_cast
      ring
    · simp [image_eq_zero_of_notMem_tsupport hxK]

end Burnett.P01
