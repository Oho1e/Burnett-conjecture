import Burnett.Analysis.BaseMarginal.IntrinsicBaseMarginal

/-! Absolute continuity and the restriction to an open vacuum region. -/
set_option autoImplicit false
set_option maxRecDepth 4700
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.F08.IntrinsicBaseMarginal

open Set Filter MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ContravariantTensor IntrinsicScalarEinstein
open Burnett.Geometry.UnitCosphere (Cosphere projection continuous_projection)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

private theorem auxiliaryEinsteinDensity_eq_zero_of_ricci_eq_zero (r : Metric (M := M))
    (B : Field (M := M)) (hn : IsNondegenerate B) (x : M)
    (hScal : intrinsicScalar B hn x = 0)
    (hRic : ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) :
    auxiliaryEinsteinDensity r B hn x = 0 := by
  have hRic' : ricciBilinearForm B x = 0 := by
    ext u v
    exact hRic u v
  rw [auxiliaryEinsteinDensity, einsteinPair, intrinsicEinstein_eq_ricci_of_scalar_zero B hn x hScal,
    hRic', contractAt_eq_sum x (tensorTangentBasis x x (mem_chart_source CoordinateSpace x))]
  simp

variable [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

theorem physicalMarginal_absolutelyContinuous (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (hMarg : μ.map projection = (ManifoldVolume.geometricMeasure B).withDensity
      (fun x => ENNReal.ofReal (auxiliaryEinsteinDensity r B hn x))) :
    μ.map projection ≪ ManifoldVolume.geometricMeasure B := by
  rw [hMarg]
  exact withDensity_absolutelyContinuous _ _

theorem physicalMeasure_zero_over_vacuumOpen (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (μ : Measure (Cosphere r))
    (hMarg : μ.map projection = (ManifoldVolume.geometricMeasure B).withDensity
      (fun x => ENNReal.ofReal (auxiliaryEinsteinDensity r B hn x)))
    (hScal : ∀ x, intrinsicScalar B hn x = 0) (U : Set M) (hU : IsOpen U)
    (hRic : ∀ x ∈ U, ∀ u v : TangentSpace Model x, IntrinsicRicciTrace.ricci B x u v = 0) :
    μ (projection ⁻¹' U) = 0 := by
  have hm : Measurable (projection (r := r)) := (continuous_projection r).measurable
  rw [← Measure.map_apply hm hU.measurableSet, hMarg, withDensity_apply _ hU.measurableSet]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [ae_restrict_mem (μ := ManifoldVolume.geometricMeasure B) hU.measurableSet] with x hx
  rw [auxiliaryEinsteinDensity_eq_zero_of_ricci_eq_zero r B hn x (hScal x) (hRic x hx)]
  exact ENNReal.ofReal_zero

end Burnett.F08.IntrinsicBaseMarginal
