import Burnett.Analysis.GaugeProjection.ProjectedChartSourceBound
import Burnett.Geometry.AuxiliaryAdmissibility
import Burnett.Geometry.IntrinsicRicciTrace
import Burnett.Geometry.OriginalAdmissibleLocalControl
import Burnett.Analysis.GeometricHminusBoundedForcing

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open Set Filter
open Burnett.RicciSymbol
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.CurvatureDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ManifoldMetricTransition (coordinateBilinear)
open scoped ContDiff Manifold NNReal Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The intrinsic covariant derivative bound controls the full raw first coordinate jet
on a fixed compact chart window, after adding the fixed background jet. -/
theorem exists_coordinateMetricFirstJet_bound_of_intrinsic
    (r : ManifoldMetric.Metric (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (hg : ∀ n, ManifoldBilinear.IsSmooth (g n)) (hg₀ : ManifoldBilinear.IsSmooth g₀)
    (hND₀ : ManifoldBilinear.IsNondegenerate g₀)
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hDh : AuxiliaryAdmissibility.CompactDhBound r g₀ g)
    (c : M) (K : Set CoordinateSpace) (hK : IsCompact K)
    (hKU : K ⊆ (chartAt CoordinateSpace c).target) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n x, x ∈ K →
      ‖coordinateJet (metricComponents (coordinateBilinear (g n) c)) x‖ ≤ C := by
  let G n := metricComponents (coordinateBilinear (g n) c)
  let G₀ := metricComponents (coordinateBilinear g₀ c)
  let U := (chartAt CoordinateSpace c).target
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  have hG n i j : ContDiffOn ℝ 1 (fun x => G n x i j) U :=
    ManifoldBilinear.contDiffOn_metricComponents_one (g n) (hg n) c i j
  have hG₀ i j : ContDiffOn ℝ 1 (fun x => G₀ x i j) U :=
    ManifoldBilinear.contDiffOn_metricComponents_one g₀ hg₀ c i j
  obtain ⟨D, hD, htail⟩ :=
    OriginalAdmissibleLocalControl.exists_eventual_rawJet_bound_of_original
      r g₀ g hg₀ hg hND₀ hconv hDh c K hK hKU
  have hContinuous n : ContinuousOn (coordinateJet (fun x => G n x - G₀ x)) K :=
    (BackgroundConnection.continuousOn_coordinateJet _ U hU
      (fun i j => (hG n i j).sub (hG₀ i j))).mono hKU
  obtain ⟨B, hB, hdiff⟩ :=
    Burnett.Analysis.GeometricHminusBoundedForcing.all_bound_of_eventual_on_compact
      (fun n => coordinateJet (fun x => G n x - G₀ x)) K hK hContinuous hD htail
  obtain ⟨B₀, hB₀⟩ := hK.exists_bound_of_continuousOn
    ((BackgroundConnection.continuousOn_coordinateJet G₀ U hU hG₀).mono hKU)
  refine ⟨B + max B₀ 0, add_nonneg hB (le_max_right _ _), ?_⟩
  intro n x hx
  have hxU : U ∈ 𝓝 x := hU.mem_nhds (hKU hx)
  have hsub := coordinateJet_sub (G n) G₀ x
    (fun i j => ((hG n i j).contDiffAt hxU).differentiableAt le_rfl)
    (fun i j => ((hG₀ i j).contDiffAt hxU).differentiableAt le_rfl)
  change ‖coordinateJet (G n) x‖ ≤ _
  calc
    _ = ‖coordinateJet (fun y => G n y - G₀ y) x + coordinateJet G₀ x‖ := by
      rw [hsub, sub_add_cancel]
    _ ≤ ‖coordinateJet (fun y => G n y - G₀ y) x‖ + ‖coordinateJet G₀ x‖ :=
      norm_add_le _ _
    _ ≤ B + max B₀ 0 := add_le_add (hdiff n x hx) ((hB₀ x hx).trans (le_max_left _ _))

variable [T2Space M]

/-- Intrinsic vacuum and admissible local control supply the projected source bound for
the original cutoff fluctuation, using the same globally chosen inverse coefficients. -/
theorem exists_projectedVacuumDivergenceL2_of_intrinsic
    (r : ManifoldMetric.Metric (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (hg : ∀ n, ManifoldBilinear.IsSmooth (g n)) (hg₀ : ManifoldBilinear.IsSmooth g₀)
    (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n))
    (hND : ∀ n, ManifoldBilinear.IsNondegenerate (g n))
    (hND₀ : ManifoldBilinear.IsNondegenerate g₀)
    (hVac : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hDh : AuxiliaryAdmissibility.CompactDhBound r g₀ g)
    (c : M) (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) (hχU : tsupport χ ⊆ (chartAt CoordinateSpace c).target)
    (a : ℕ → CoordinateSpace → Tensor2) (ha : ∀ n, SmoothCoordinateComponents (a n))
    (L : ℝ≥0) (hL : ∀ n i j, LipschitzWith L (fun x => a n x i j))
    (hInv : ∀ n, a n =ᶠ[𝓝ˢ (tsupport χ)]
      projectedChartInverse (metricComponents (coordinateBilinear (g n) c))) :
    let G n := metricComponents (coordinateBilinear (g n) c)
    let G₀ := metricComponents (coordinateBilinear g₀ c)
    ∃ R : ProjectedChartRepresentatives G a G₀ (tsupport χ),
      let z (n : ℕ) := localizedMetricSchwartz (R.metric n) R.background χ hχ hc
        (R.metric_smooth n) R.background_smooth
      (∀ n i j x, z n i j x = ((χ x * (G n x i j - G₀ x i j) : ℝ) : ℂ)) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n,
        ‖projectedSourceDivergenceL2 (ProjectedSourceCoefficients.ofReal
          (fun i j x => a n x i j) (ha n) L (hL n)) (projectionFullSchwartz (z n))‖ ≤ C := by
  dsimp only
  let U := (chartAt CoordinateSpace c).target
  let G n := metricComponents (coordinateBilinear (g n) c)
  let G₀ := metricComponents (coordinateBilinear g₀ c)
  have hU : IsOpen U := (chartAt CoordinateSpace c).open_target
  have hG n i j : ContDiffOn ℝ ∞ (fun x => G n x i j) U :=
    ManifoldBilinear.contDiffOn_metricComponents (g n) (hg n) c i j
  have hG₀ i j : ContDiffOn ℝ ∞ (fun x => G₀ x i j) U :=
    ManifoldBilinear.contDiffOn_metricComponents g₀ hg₀ c i j
  have hSym n x : IsSymmetricTensor (G n x) :=
    FiberMetric.covariant_symmetric _
      (ManifoldBilinear.coordinateBilinear_symmetric (g n) (hs n) c x) coordinateBasis
  have hDet n x (hx : x ∈ U) : (Matrix.of (G n x)).det ≠ 0 :=
    ManifoldVolumeRegularity.coordinate_det_ne_zero (g n) (hND n) c hx
  have hDet₀ x (hx : x ∈ U) : (Matrix.of (G₀ x)).det ≠ 0 :=
    ManifoldVolumeRegularity.coordinate_det_ne_zero g₀ hND₀ c hx
  have hLocalVac n x (hx : x ∈ tsupport χ) i j : coordinateRicci
      (fun y => christoffel (projectedChartInverse (G n) y) (coordinateJet (G n) y)) x i j = 0 :=
    IntrinsicRicciTrace.sequence_coordinateVacuum_of_intrinsic g hg hs hND hVac c n x
      (hχU hx) i j
  have hChartConv :=
    ManifoldMetricSequence.components_uniform_of_physical_C0loc r g g₀ hconv c (tsupport χ) hc hχU
  obtain ⟨D, _, hD⟩ :=
    exists_coordinateMetricFirstJet_bound_of_intrinsic r g g₀ hg hg₀ hND₀ hconv hDh c
      (tsupport χ) hc hχU
  exact exists_projectedVacuumDivergenceL2_of_openChart U hU χ hχ hc hχU G a G₀ hG hG₀
    (fun n x _ => hSym n x) hDet hDet₀ ha L hL hInv hLocalVac hChartConv D hD

end Burnett.P01
