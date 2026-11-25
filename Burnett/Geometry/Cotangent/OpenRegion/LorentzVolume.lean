import Burnett.Geometry.Cotangent.OpenRegion.Metrics
import Burnett.Geometry.ManifoldVolumeRegularity

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter MeasureTheory
open TopologicalSpace (Opens)
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- The geometric volume of an open submanifold is the original geometric
volume on the same sets. Both sides use the same Lorentz determinant density. -/
theorem geometricMeasure_openSubtype_comap (U : Opens M) (g : Field (M := M)) :
    (ManifoldVolume.geometricMeasure g).comap (Subtype.val : U → M) =
      ManifoldVolume.geometricMeasure (restrictBilinear U g) := by
  apply ManifoldVolume.measures_eq_of_chart_restrict
  intro c
  ext A hA
  let e := chartAt E c
  let E₀ := chartAt E c.val
  let V := A ∩ e.source
  have hV : MeasurableSet V := hA.inter e.open_source.measurableSet
  have hVs : V ⊆ e.source := inter_subset_right
  let m := U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hVm : MeasurableSet (Subtype.val '' V : Set M) := m.measurableSet_image.mpr hV
  have hVsm : (Subtype.val '' V : Set M) ⊆ E₀.source := by
    rintro x ⟨q, hq, rfl⟩
    exact (hVs hq).2
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  trans ManifoldVolume.geometricMeasure g (Subtype.val '' V)
  · exact m.comap_apply (ManifoldVolume.geometricMeasure g) V
  rw [ManifoldVolumeRegularity.geometricMeasure_apply_of_subset_chart g c.val hVm hVsm,
    ManifoldVolumeRegularity.geometricMeasure_apply_of_subset_chart (restrictBilinear U g) c hV hVs]
  have hImg : E₀ '' (Subtype.val '' V : Set M) = e '' V := by
    rw [image_image]
    rfl
  rw [hImg]
  let W := e '' V
  have hW : MeasurableSet W := by
    have hW' : W = (ManifoldVolume.inverseChart c) ⁻¹' V ∩ e.target := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        refine ⟨?_, e.mapsTo (hVs hx)⟩
        change ManifoldVolume.inverseChart c (chartAt E c x) ∈ V
        rwa [ManifoldVolume.inverseChart_chart c (hVs hx)]
      · rintro ⟨hv, hy⟩
        rw [mem_preimage, ManifoldVolume.inverseChart_of_mem c hy] at hv
        exact ⟨e.symm y, hv, e.right_inv hy⟩
    rw [hW']
    exact ((ManifoldVolume.measurable_inverseChart c) hV).inter e.open_target.measurableSet
  have hWt : W ⊆ e.target := by
    rintro y ⟨x, hx, rfl⟩
    exact e.mapsTo (hVs hx)
  change ManifoldVolume.coordinateMeasure g c.val W = ManifoldVolume.coordinateMeasure (restrictBilinear U g) c W
  unfold ManifoldVolume.coordinateMeasure LorentzVolume.coordinateMeasure
  rw [withDensity_apply _ hW, withDensity_apply _ hW]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hW] with y hy
  have hB := coordinateBilinear_openSubtype U g c (hWt hy)
  simp only [LorentzVolume.density, metricComponents, hB]

/-- Pushing the region volume forward along its inclusion gives exactly the
restriction of the original geometric measure to that region. -/
theorem geometricMeasure_openSubtype_map (U : Opens M) (g : Field (M := M)) :
    (ManifoldVolume.geometricMeasure (restrictBilinear U g)).map (Subtype.val : U → M) =
      (ManifoldVolume.geometricMeasure g).restrict U := by
  rw [← geometricMeasure_openSubtype_comap U g]
  have e : MeasurableEmbedding (Subtype.val : U → M) := U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding
  have hRange : range (Subtype.val : U → M) = (U : Set M) := by
    ext x
    exact ⟨fun ⟨y, hy⟩ => hy ▸ y.property, fun hx => ⟨⟨x, hx⟩, rfl⟩⟩
  exact (e.map_comap (ManifoldVolume.geometricMeasure g)).trans (congrArg _ hRange)

end Burnett.Geometry.OpenRegion
