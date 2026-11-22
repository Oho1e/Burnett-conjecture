import Burnett.Analysis.GaugeProjection.MaximalChartFirstJet
import Burnett.Analysis.GaugeProjection.UniformIntrinsicProjectedSource
import Burnett.Geometry.MaximalChart.VacuumTransfer

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.P01

open Filter Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference CurvatureDifference MaximalChart ManifoldMetric
open private coordinate_opNorm_le from Burnett.Analysis.GaugeProjection.IntrinsicChartProjectedNorms
open scoped Manifold ContDiff Topology NNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- In any chart of the smooth maximal atlas, the actual cutoff metric perturbation has
all the projected norm limits and a whole-space source bound uniform over inverse-metric
extensions with a given common Lipschitz bound. -/
theorem exists_maximalChartProjectedField_norms_and_uniform_source
    (r : ManifoldMetric.Metric (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M)) (B : ManifoldBilinear.Field (M := M))
    (hg : ∀ n, ManifoldBilinear.IsSmooth (g n)) (hB : ManifoldBilinear.IsSmooth B)
    (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n)) (hn : ∀ n, ManifoldBilinear.IsNondegenerate (g n))
    (hBn : ManifoldBilinear.IsNondegenerate B) (hVac : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g B)
    (hDh : AuxiliaryAdmissibility.CompactDhBound r B g)
    (d : OpenPartialHomeomorph M CoordinateSpace) (hd : d ∈ IsManifold.maximalAtlas Model ∞ M)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχd : tsupport χ ⊆ d.target) :
    let c : AtlasChart M := ⟨d, hd⟩
    let G n := metricComponents (fixedForm (g n) c)
    let G₀ := metricComponents (fixedForm B c)
    ∃ z : ℕ → ProjectionSchwartzMatrix,
      (∀ n x i j, z n i j x = ((χ x * (G n x i j - G₀ x i j) : ℝ) : ℂ)) ∧
      ProjectedFieldNormLimits (fun n => projectionFullSchwartz (z n)) ∧
      ∀ L : ℝ≥0, ∃ C : ℝ, 0 ≤ C ∧
        ∀ (a : ℕ → CoordinateSpace → Tensor2) (ha : ∀ n, SmoothCoordinateComponents (a n))
          (hL : ∀ n i j, LipschitzWith L (fun x => a n x i j)),
          (∀ n, a n =ᶠ[𝓝ˢ (tsupport χ)] projectedChartInverse (G n)) →
          ∀ n, ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
            (fun i j x => a n x i j) (ha n) L (hL n)) (projectionFullSchwartz (z n))‖ ≤ C := by
  intro c G G₀
  let K := tsupport χ
  have hG n i j : ContDiffOn ℝ ∞ (fun x => G n x i j) d.target :=
    fixedForm_components_smooth (g n) (hg n) c i j
  have hG₀ i j : ContDiffOn ℝ ∞ (fun x => G₀ x i j) d.target :=
    fixedForm_components_smooth B hB c i j
  have hConv : TendstoUniformlyOn G G₀ atTop K := fixed_components_uniform_of_physical_C0loc r g B hconv c K hc hχd
  obtain ⟨A, hA, hJet⟩ := fixedJet_uniform_bound_on_compact r g B hg hB hBn hconv hDh c hc hχd
  have hDiff (n : ℕ) (i j : Index) (x : CoordinateSpace) (hx : x ∈ K) :
      ‖fderiv ℝ (fun y => G n y i j - G₀ y i j) x‖ ≤ 4 * A := by
    apply coordinate_opNorm_le _ A hA
    intro b
    let J := coordinateJet (fun y => G n y - G₀ y) x
    change ‖J b i j‖ ≤ A
    exact (norm_le_pi_norm (J b i) j).trans ((norm_le_pi_norm (J b) i).trans
      ((norm_le_pi_norm J b).trans (hJet n x hx)))
  obtain ⟨z, hz, hNorm⟩ := exists_openChartProjectedField_norms d.open_target G G₀ hG hG₀
    χ hχ hc hχd hConv ⟨4 * A, by positivity⟩ hDiff
  refine ⟨z, hz, hNorm, projectedSource_uniform_extension_bound K _ z ?_ ?_⟩
  · intro n i j
    apply closure_minimal _ isClosed_closure
    intro x hx
    apply subset_tsupport χ
    intro hzero
    apply hx
    rw [hz n x i j, hzero, zero_mul, Complex.ofReal_zero]
  intro a ha L hL hInv
  obtain ⟨D, _, hD⟩ := fixedForm_firstJet_uniform_bound_on_compact r g B hg hB hBn hconv hDh c hc hχd
  have hV (n : ℕ) (x : CoordinateSpace) (hx : x ∈ K) (i j : Index) :
      coordinateRicci (fun y => christoffel (projectedChartInverse (G n) y) (coordinateJet (G n) y)) x i j = 0 :=
    fixedForm_coordinateVacuum_of_intrinsic (g n) (hg n) (hs n) (hn n) (hVac n) c x (hχd hx) i j
  obtain ⟨R, hR, C, hC, hSource⟩ := exists_projectedVacuumDivergenceL2_of_openChart
    d.target d.open_target χ hχ hc hχd G a G₀ hG hG₀ (fun n x _ i j => hs n (d.symm x) _ _)
    (fun n _ hx => fixedForm_det_ne_zero (g n) (hn n) c hx) (fun _ hx => fixedForm_det_ne_zero B hBn c hx)
    ha L hL hInv hV hConv D hD
  refine ⟨C, hC, fun n => ?_⟩
  have he : localizedMetricSchwartz (R.metric n) R.background χ hχ hc (R.metric_smooth n)
      R.background_smooth = z n := by
    funext i j
    ext x
    exact (hR n i j x).trans (hz n x i j).symm
  rw [← he]
  exact hSource n

end Burnett.P01
