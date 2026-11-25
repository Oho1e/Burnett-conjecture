import Burnett.Analysis.Microlocal.Overlap.ReceivingChartVolumeInputs
import Burnett.Geometry.ManifoldVolume

/-! The actual geometric volume in every compatible receiving chart. -/

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Filter Classical Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart ChartVolume
open scoped Manifold ContDiff Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [MeasurableSpace M] [BorelSpace M]

/-- The actual Lorentzian density of the background tensor in a receiving chart. -/
def receivingCoordinateVolume (B : Field (M := M)) (c : AtlasChart M) : Measure E :=
  LorentzVolume.coordinateMeasure (metricComponents (fixedForm B c))

omit [MeasurableSpace M] [BorelSpace M] in
theorem receivingCoordinateVolume_transition (B : Field (M := M)) (c d : AtlasChart M) :
    Measure.map (c.transition d) ((receivingCoordinateVolume B c).restrict (c.transition d).source) =
      (receivingCoordinateVolume B d).restrict (c.transition d).target := by
  let e := c.transition d
  have hd : DifferentiableOn ℝ e e.source := (c.smooth_transition d).differentiableOn (by simp)
  change Measure.map e ((receivingCoordinateVolume B c).restrict e.source) =
    (receivingCoordinateVolume B d).restrict e.target
  rw [← e.image_source_eq_target]
  refine LorentzVolume.map_coordinateMeasure_restrict_of_pullback
    (metricComponents (fixedForm B d)) (metricComponents (fixedForm B c))
    e (fderiv ℝ e) e.source e.open_source.measurableSet ?_ e.injOn ?_
  · intro x hx
    exact ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact fixedForm_matrix_change B c d hx

omit [MeasurableSpace M] [BorelSpace M] in
private theorem receivingCoordinateVolume_atPoint (B : Field (M := M)) (q : M) :
    (receivingCoordinateVolume B (.atPoint q)).restrict (chartAt E q).target =
      (ManifoldVolume.coordinateMeasure B q).restrict (chartAt E q).target := by
  have hU := (chartAt E q).open_target.measurableSet
  simp only [receivingCoordinateVolume, ManifoldVolume.coordinateMeasure,
    LorentzVolume.coordinateMeasure, restrict_withDensity hU]
  refine withDensity_congr_ae ?_
  filter_upwards [ae_restrict_mem (μ := volume) hU] with x hx
  simp only [LorentzVolume.density, fixedForm_eq_preferred_components B q hx]

section
variable [Nonempty M]

/-- The inverse used for integration is measurable on the whole coordinate space. -/
def receivingVolumeInverse (c : AtlasChart M) (x : E) : M :=
  c.chart.target.piecewise c.chart.symm (fun _ => Classical.choice ‹Nonempty M›) x

omit [IsManifold Model ∞ M] in
theorem measurable_receivingVolumeInverse (c : AtlasChart M) : Measurable (receivingVolumeInverse c) :=
  c.chart.continuousOn_symm.measurable_piecewise continuousOn_const c.chart.open_target.measurableSet

omit [IsManifold Model ∞ M] [MeasurableSpace M] [BorelSpace M] in
theorem receivingVolumeInverse_of_mem (c : AtlasChart M) {x : E} (hx : x ∈ c.chart.target) :
    receivingVolumeInverse c x = c.chart.symm x := piecewise_eq_of_mem _ _ _ hx

private def pushedReceivingVolume (B : Field (M := M)) (c : AtlasChart M) : Measure M :=
  Measure.map (receivingVolumeInverse c) ((receivingCoordinateVolume B c).restrict c.chart.target)

omit [IsManifold Model ∞ M] in
private theorem pushedReceivingVolume_restrict (B : Field (M := M)) (c : AtlasChart M)
    (S : Set M) (hS : MeasurableSet S) :
    (pushedReceivingVolume B c).restrict S =
      Measure.map (receivingVolumeInverse c)
        ((receivingCoordinateVolume B c).restrict (c.chart.target ∩ c.chart.symm ⁻¹' S)) := by
  rw [pushedReceivingVolume, Measure.restrict_map (measurable_receivingVolumeInverse c) hS,
    Measure.restrict_restrict ((measurable_receivingVolumeInverse c) hS)]
  congr 2
  ext x
  by_cases hx : x ∈ c.chart.target <;> simp [receivingVolumeInverse, hx, and_comm]

omit [IsManifold Model ∞ M] in
private theorem pushedReceivingVolume_restrict_source (B : Field (M := M)) (c : AtlasChart M) :
    (pushedReceivingVolume B c).restrict c.chart.source = pushedReceivingVolume B c := by
  have he : c.chart.target ∩ c.chart.symm ⁻¹' c.chart.source = c.chart.target :=
    inter_eq_left.mpr c.chart.symm_mapsTo
  rw [pushedReceivingVolume_restrict B c _ c.chart.open_source.measurableSet, he]
  rfl

omit [IsManifold Model ∞ M] in
private theorem pushedReceivingVolume_restrict_overlap (B : Field (M := M)) (c d : AtlasChart M) :
    (pushedReceivingVolume B c).restrict (c.chart.source ∩ d.chart.source) =
      Measure.map (receivingVolumeInverse c)
        ((receivingCoordinateVolume B c).restrict (c.transition d).source) := by
  rw [pushedReceivingVolume_restrict B c _ (c.chart.open_source.measurableSet.inter d.chart.open_source.measurableSet)]
  congr 2
  ext x
  change (x ∈ c.chart.target ∧ c.chart.symm x ∈ c.chart.source ∩ d.chart.source) ↔
    (x ∈ c.chart.target ∧ c.chart.symm x ∈ d.chart.source)
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, c.chart.symm_mapsTo h.1, h.2⟩⟩

private theorem pushedReceivingVolume_compatible (B : Field (M := M)) (c d : AtlasChart M) :
    (pushedReceivingVolume B c).restrict (c.chart.source ∩ d.chart.source) =
      (pushedReceivingVolume B d).restrict (c.chart.source ∩ d.chart.source) := by
  let e := c.transition d
  have hmap := receivingCoordinateVolume_transition B c d
  have heae : AEMeasurable e ((receivingCoordinateVolume B c).restrict e.source) :=
    (c.smooth_transition d).continuousOn.aemeasurable e.open_source.measurableSet
  calc
    _ = Measure.map (receivingVolumeInverse c) ((receivingCoordinateVolume B c).restrict e.source) :=
      pushedReceivingVolume_restrict_overlap B c d
    _ = Measure.map (receivingVolumeInverse d) ((receivingCoordinateVolume B d).restrict e.target) := by
      rw [← hmap, AEMeasurable.map_map_of_aemeasurable (measurable_receivingVolumeInverse d).aemeasurable heae]
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem e.open_source.measurableSet] with x hx
      rw [Function.comp_apply, receivingVolumeInverse_of_mem c hx.1,
        receivingVolumeInverse_of_mem d (e.mapsTo hx).1]
      exact (d.chart.left_inv hx.2).symm
    _ = _ := by
      rw [inter_comm c.chart.source d.chart.source, pushedReceivingVolume_restrict_overlap B d c]
      rfl

omit [BorelSpace M] in
private theorem pushedReceivingVolume_atPoint (B : Field (M := M)) (q : M) :
    pushedReceivingVolume B (.atPoint q) = ManifoldVolume.localMeasure B q := by
  unfold pushedReceivingVolume ManifoldVolume.localMeasure ManifoldVolume.transport
  change Measure.map (receivingVolumeInverse (.atPoint q))
    ((receivingCoordinateVolume B (.atPoint q)).restrict (chartAt E q).target) = _
  rw [receivingCoordinateVolume_atPoint B q]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (chartAt E q).open_target.measurableSet] with x hx
  rw [receivingVolumeInverse_of_mem (.atPoint q) hx, ManifoldVolume.inverseChart_of_mem q hx]
  rfl

variable [SecondCountableTopology M]

/-- The actual glued geometric measure restricts to the pushed local measure of any chart. -/
theorem geometricVolume_restrict_eq_receiving (B : Field (M := M)) (c : AtlasChart M) :
    (ManifoldVolume.geometricMeasure B).restrict c.chart.source =
      Measure.map (receivingVolumeInverse c) ((receivingCoordinateVolume B c).restrict c.chart.target) := by
  change _ = pushedReceivingVolume B c
  apply ManifoldVolume.measures_eq_of_chart_restrict
  intro q
  let d : AtlasChart M := .atPoint q
  change ((ManifoldVolume.geometricMeasure B).restrict c.chart.source).restrict d.chart.source =
    (pushedReceivingVolume B c).restrict d.chart.source
  rw [← pushedReceivingVolume_restrict_source B c]
  rw [Measure.restrict_restrict d.chart.open_source.measurableSet,
    Measure.restrict_restrict d.chart.open_source.measurableSet, inter_comm d.chart.source c.chart.source,
    pushedReceivingVolume_compatible B c d, pushedReceivingVolume_atPoint B q]
  rw [← ManifoldVolume.geometricMeasure_restrict B q, inter_comm c.chart.source d.chart.source,
    Measure.restrict_restrict (d.chart.open_source.measurableSet.inter c.chart.open_source.measurableSet)]
  change _ = (ManifoldVolume.geometricMeasure B).restrict ((d.chart.source ∩ c.chart.source) ∩ d.chart.source)
  rw [inter_eq_left.mpr inter_subset_left]

/-- This formula uses the actual background volume, with no choice of chartwise measure. -/
theorem map_chart_geometricVolume_receiving (B : Field (M := M)) (c : AtlasChart M) :
    Measure.map c.chart ((ManifoldVolume.geometricMeasure B).restrict c.chart.source) =
      (receivingCoordinateVolume B c).restrict c.chart.target := by
  have hc : AEMeasurable c.chart (pushedReceivingVolume B c) := by
    have h := c.chart.continuousOn.aemeasurable (μ := pushedReceivingVolume B c)
      c.chart.open_source.measurableSet
    rwa [pushedReceivingVolume_restrict_source B c] at h
  rw [geometricVolume_restrict_eq_receiving B c]
  change AEMeasurable c.chart (Measure.map (receivingVolumeInverse c)
    ((receivingCoordinateVolume B c).restrict c.chart.target)) at hc
  rw [AEMeasurable.map_map_of_aemeasurable hc (measurable_receivingVolumeInverse c).aemeasurable]
  trans Measure.map id ((receivingCoordinateVolume B c).restrict c.chart.target)
  · apply Measure.map_congr
    filter_upwards [ae_restrict_mem c.chart.open_target.measurableSet] with x hx
    rw [Function.comp_apply, receivingVolumeInverse_of_mem c hx, id_eq, c.chart.right_inv hx]
  · exact Measure.map_id

end
end Burnett.Microlocal.Overlap
