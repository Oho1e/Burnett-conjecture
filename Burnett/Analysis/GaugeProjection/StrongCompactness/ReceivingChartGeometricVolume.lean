import Burnett.Geometry.MaximalChart.MetricCoordinates

/-! The original geometric volume in an arbitrary compatible receiving chart. -/

set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 4000000

noncomputable section
namespace Burnett.Geometry.MaximalChart

open Set Filter MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ChartVolume
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The coordinate measure of the actual background metric in a smooth atlas chart. -/
def atlasCoordinateMeasure (B : Field (M := M)) (c : AtlasChart M) : Measure CoordinateSpace :=
  LorentzVolume.coordinateMeasure (metricComponents (fixedForm B c))

/-- The measurable extension of the inverse chart agrees with the original inverse on the chart target. -/
def atlasVolumeInverse (c : AtlasChart M) (x : CoordinateSpace) : M := by
  classical
  exact c.chart.target.piecewise c.chart.symm (fun _ => c.chart.symm 0) x

omit [IsManifold Model ∞ M] in
theorem atlasVolumeInverse_of_mem (c : AtlasChart M) {x : CoordinateSpace} (hx : x ∈ c.chart.target) :
    atlasVolumeInverse c x = c.chart.symm x := by
  classical
  simp only [atlasVolumeInverse, piecewise_eq_of_mem _ _ _ hx]

theorem atlasCoordinateMeasure_change (B : Field (M := M)) (c d : AtlasChart M) :
    Measure.map (c.transition d) ((atlasCoordinateMeasure B c).restrict (c.transition d).source) =
      (atlasCoordinateMeasure B d).restrict (c.transition d).target := by
  let e := c.transition d
  have hd : DifferentiableOn ℝ e e.source := (c.smooth_transition d).differentiableOn (by simp)
  rw [← e.image_source_eq_target]
  apply LorentzVolume.map_coordinateMeasure_restrict_of_pullback _ _ e (fderiv ℝ e) e.source
    e.open_source.measurableSet _ e.injOn (fun x hx => fixedForm_matrix_change B c d hx)
  intro x hx
  exact ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt

variable [MeasurableSpace M] [BorelSpace M]

omit [IsManifold Model ∞ M] in
theorem measurable_atlasVolumeInverse (c : AtlasChart M) : Measurable (atlasVolumeInverse c) := by
  classical
  exact c.chart.continuousOn_symm.measurable_piecewise continuousOn_const c.chart.open_target.measurableSet

private def atlasLocalMeasure (B : Field (M := M)) (c : AtlasChart M) : Measure M :=
  Measure.map (atlasVolumeInverse c) ((atlasCoordinateMeasure B c).restrict c.chart.target)

omit [IsManifold Model ∞ M] in
private theorem atlasLocalMeasure_restrict (B : Field (M := M)) (c : AtlasChart M)
    (V : Set M) (hV : MeasurableSet V) :
    (atlasLocalMeasure B c).restrict V = Measure.map (atlasVolumeInverse c)
      ((atlasCoordinateMeasure B c).restrict (c.chart.target ∩ c.chart.symm ⁻¹' V)) := by
  rw [atlasLocalMeasure, Measure.restrict_map (measurable_atlasVolumeInverse c) hV,
    Measure.restrict_restrict ((measurable_atlasVolumeInverse c) hV)]
  congr 2
  ext y
  by_cases hy : y ∈ c.chart.target
  · simp [hy, atlasVolumeInverse_of_mem c hy]
  · simp [hy]

omit [IsManifold Model ∞ M] in
private theorem atlasLocalMeasure_restrict_source (B : Field (M := M)) (c : AtlasChart M) :
    (atlasLocalMeasure B c).restrict c.chart.source = atlasLocalMeasure B c := by
  have he : c.chart.target ∩ c.chart.symm ⁻¹' c.chart.source = c.chart.target :=
    inter_eq_left.mpr c.chart.symm_mapsTo
  rw [atlasLocalMeasure_restrict B c _ c.chart.open_source.measurableSet,
    he]
  rfl

omit [BorelSpace M] in
private theorem atlasLocalMeasure_preferred (B : Field (M := M)) (q : M) :
    atlasLocalMeasure B (.atPoint q) = ManifoldVolume.localMeasure B q := by
  let e := chartAt CoordinateSpace q
  have hν : (atlasCoordinateMeasure B (.atPoint q)).restrict e.target =
      (ManifoldVolume.coordinateMeasure B q).restrict e.target := by
    change ((volume : Measure CoordinateSpace).withDensity _).restrict e.target = (volume.withDensity _).restrict e.target
    rw [restrict_withDensity e.open_target.measurableSet, restrict_withDensity e.open_target.measurableSet]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure CoordinateSpace)) e.open_target.measurableSet] with x hx
    simp only [LorentzVolume.density, fixedForm_eq_preferred_components B q hx]
  unfold atlasLocalMeasure ManifoldVolume.localMeasure ManifoldVolume.transport
  change Measure.map (atlasVolumeInverse (.atPoint q)) ((atlasCoordinateMeasure B (.atPoint q)).restrict e.target) = _
  rw [hν]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := ManifoldVolume.coordinateMeasure B q) e.open_target.measurableSet] with x hx
  exact (atlasVolumeInverse_of_mem (.atPoint q) hx).trans (ManifoldVolume.inverseChart_of_mem q hx).symm

omit [IsManifold Model ∞ M] in
private theorem atlasLocalMeasure_restrict_overlap (B : Field (M := M)) (c d : AtlasChart M) :
    (atlasLocalMeasure B c).restrict (c.chart.source ∩ d.chart.source) =
      Measure.map (atlasVolumeInverse c) ((atlasCoordinateMeasure B c).restrict (c.transition d).source) := by
  rw [atlasLocalMeasure_restrict B c _ (c.chart.open_source.measurableSet.inter d.chart.open_source.measurableSet)]
  congr 2
  ext y
  change (y ∈ c.chart.target ∧ c.chart.symm y ∈ c.chart.source ∩ d.chart.source) ↔
    (y ∈ c.chart.target ∧ c.chart.symm y ∈ d.chart.source)
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, c.chart.symm_mapsTo h.1, h.2⟩⟩

private theorem atlasLocalMeasure_overlap (B : Field (M := M)) (c d : AtlasChart M) :
    (atlasLocalMeasure B c).restrict (c.chart.source ∩ d.chart.source) =
      (atlasLocalMeasure B d).restrict (c.chart.source ∩ d.chart.source) := by
  let e := c.transition d
  have he : e.symm = d.transition c := by
    simp only [e, AtlasChart.transition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hMap : Measure.map e ((atlasCoordinateMeasure B c).restrict e.source) =
      (atlasCoordinateMeasure B d).restrict e.target := atlasCoordinateMeasure_change B c d
  have hE : AEMeasurable e ((atlasCoordinateMeasure B c).restrict e.source) :=
    (c.smooth_transition d).continuousOn.aemeasurable e.open_source.measurableSet
  rw [atlasLocalMeasure_restrict_overlap B c d, inter_comm c.chart.source d.chart.source,
    atlasLocalMeasure_restrict_overlap B d c, ← he]
  change _ = Measure.map (atlasVolumeInverse d) ((atlasCoordinateMeasure B d).restrict e.target)
  rw [← hMap, AEMeasurable.map_map_of_aemeasurable (measurable_atlasVolumeInverse d).aemeasurable hE]
  apply Measure.map_congr
  filter_upwards [ae_restrict_mem (μ := atlasCoordinateMeasure B c) e.open_source.measurableSet] with y hy
  simp only [Function.comp_apply, atlasVolumeInverse_of_mem c hy.1, atlasVolumeInverse_of_mem d (e.mapsTo hy).1]
  exact (d.chart.left_inv hy.2).symm

variable [SecondCountableTopology M]

/-- The local coordinate density in any smooth atlas chart is the same global geometric measure on its source. -/
theorem geometricMeasure_restrict_atlasSource (B : Field (M := M)) (c : AtlasChart M) :
    (ManifoldVolume.geometricMeasure B).restrict c.chart.source =
      Measure.map (atlasVolumeInverse c) ((atlasCoordinateMeasure B c).restrict c.chart.target) := by
  let V := ManifoldVolume.geometricMeasure B
  change V.restrict c.chart.source = atlasLocalMeasure B c
  apply ManifoldVolume.measures_eq_of_chart_restrict
  intro q
  let d := AtlasChart.atPoint q
  have hD : V.restrict d.chart.source = atlasLocalMeasure B d :=
    (ManifoldVolume.geometricMeasure_restrict B q).trans (atlasLocalMeasure_preferred B q).symm
  have hCsource : (atlasLocalMeasure B c).restrict d.chart.source =
      (atlasLocalMeasure B c).restrict (c.chart.source ∩ d.chart.source) := by
    rw [inter_comm, ← Measure.restrict_restrict' c.chart.open_source.measurableSet,
      atlasLocalMeasure_restrict_source B c]
  have hDsource : (atlasLocalMeasure B d).restrict c.chart.source =
      (atlasLocalMeasure B d).restrict (c.chart.source ∩ d.chart.source) := by
    rw [← Measure.restrict_restrict' d.chart.open_source.measurableSet, atlasLocalMeasure_restrict_source B d]
  change (V.restrict c.chart.source).restrict d.chart.source = (atlasLocalMeasure B c).restrict d.chart.source
  rw [Measure.restrict_comm d.chart.open_source.measurableSet, hD, hDsource, hCsource]
  exact (atlasLocalMeasure_overlap B c d).symm

/-- On a compact chart window, the original geometric measure pulls back the actual coordinate volume exactly. -/
theorem geometricMeasure_restrict_atlasCompactWindow [T2Space M]
    (B : Field (M := M)) (c : AtlasChart M) {K : Set CoordinateSpace}
    (hK : IsCompact K) (hKt : K ⊆ c.chart.target) :
    (ManifoldVolume.geometricMeasure B).restrict (c.chart.symm '' K) =
      Measure.map (atlasVolumeInverse c) ((atlasCoordinateMeasure B c).restrict K) := by
  let L := c.chart.symm '' K
  have hL : IsCompact L := hK.image_of_continuousOn (c.chart.continuousOn_symm.mono hKt)
  have hLs : L ⊆ c.chart.source := image_subset_iff.mpr (c.chart.symm_mapsTo.mono_left hKt)
  rw [← Measure.restrict_restrict_of_subset hLs, geometricMeasure_restrict_atlasSource B c]
  change (atlasLocalMeasure B c).restrict L = _
  rw [atlasLocalMeasure_restrict B c L hL.measurableSet]
  congr 2
  ext y
  constructor
  · rintro ⟨hy, z, hz, he⟩
    have hzy := c.chart.symm.injOn (hKt hz) hy he
    rwa [← hzy]
  · intro hy
    exact ⟨hKt hy, y, hy, rfl⟩

end Burnett.Geometry.MaximalChart
