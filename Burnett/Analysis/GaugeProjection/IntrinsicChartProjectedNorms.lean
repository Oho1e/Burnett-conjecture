import Burnett.Analysis.GaugeProjection.OpenChartProjectedNorms
import Burnett.Analysis.Microlocal.OriginalCoordinateCurl
import Burnett.Geometry.AuxiliaryAdmissibility

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open Set Filter
open Burnett.RicciSymbol
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ManifoldMetricTransition (coordinateBilinear)
open scoped ContDiff Manifold NNReal Topology

private theorem coordinate_opNorm_le (D : CoordinateSpace →L[ℝ] ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hD : ∀ b : Index, ‖D (EuclideanSpace.single b 1)‖ ≤ C) :
    ‖D‖ ≤ 4 * C := by
  apply D.opNorm_le_bound (by positivity)
  intro v
  have hExpand : D v = ∑ b, v b * D (EuclideanSpace.single b 1) := by
    have h := congrArg D (coordinateBasis.sum_repr v)
    simpa only [map_sum, map_smul, smul_eq_mul, coordinateBasis,
      OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
      OrthonormalBasis.coe_toBasis, EuclideanSpace.basisFun_apply] using h.symm
  rw [hExpand]
  calc
    _ ≤ ∑ b : Index, ‖v b * D (EuclideanSpace.single b 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _ : Index, ‖v‖ * C := by
      apply Finset.sum_le_sum
      intro b _
      rw [norm_mul]
      exact mul_le_mul (PiLp.norm_apply_le v b) (hD b) (norm_nonneg _) (norm_nonneg _)
    _ = _ := by simp [nsmul_eq_mul]; ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M]

/-- The cutoff of the original metric component differences supplies a single
Schwartz matrix sequence with all the projected whole-space norm limits. -/
theorem exists_intrinsicChartProjectedField_norms
    (r : ManifoldMetric.Metric (M := M))
    (g : ℕ → ManifoldBilinear.Field (M := M)) (g₀ : ManifoldBilinear.Field (M := M))
    (hg : ∀ n, ManifoldBilinear.IsSmooth (g n)) (hg₀ : ManifoldBilinear.IsSmooth g₀)
    (hND₀ : ManifoldBilinear.IsNondegenerate g₀)
    (hconv : ManifoldMetricSequence.LocallyUniformlyConverges r g g₀)
    (hDh : AuxiliaryAdmissibility.CompactDhBound r g₀ g)
    (c : M) (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ (chartAt CoordinateSpace c).target) :
    let G n := metricComponents (coordinateBilinear (g n) c)
    let G₀ := metricComponents (coordinateBilinear g₀ c)
    ∃ z : ℕ → ProjectionSchwartzMatrix,
      (∀ n x i j, z n i j x = ((χ x * (G n x i j - G₀ x i j) : ℝ) : ℂ)) ∧
      ProjectedFieldNormLimits (fun n => projectionFullSchwartz (z n)) := by
  let G n := metricComponents (coordinateBilinear (g n) c)
  let G₀ := metricComponents (coordinateBilinear g₀ c)
  have hConv := ManifoldMetricSequence.components_uniform_of_physical_C0loc
    r g g₀ hconv c (tsupport χ) hχc hχU
  obtain ⟨C, hC, hRaw⟩ :=
    Burnett.F05.OriginalCoordinateCurl.exists_rawComponentDerivative_bound_of_original
      r g₀ g hg₀ hg hND₀ hconv hDh c (tsupport χ) hχc hχU
  apply exists_openChartProjectedField_norms (chartAt CoordinateSpace c).open_target G G₀
    (fun n i j => ManifoldBilinear.contDiffOn_metricComponents (g n) (hg n) c i j)
    (ManifoldBilinear.contDiffOn_metricComponents g₀ hg₀ c)
    χ hχ hχc hχU hConv ⟨4 * C, by positivity⟩
  intro n i j x hx
  apply coordinate_opNorm_le _ C hC
  exact fun b => hRaw n (i, j) b x hx

end Burnett.P01
