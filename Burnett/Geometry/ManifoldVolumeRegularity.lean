import Burnett.Geometry.ManifoldVolume
import Burnett.Geometry.ManifoldBilinear

/-!
# Local finiteness and positive open sets for the actual manifold measure

The measure is the proved global `ManifoldVolume.geometricMeasure`, whose
preferred-chart formula transports the same bilinear field's actual
sqrt(abs(det)) coordinate density. Smoothness is the genuine global Hom
section condition. Continuity bounds this density on compact subsets of a
chart target; chart transport then gives a finite neighborhood at every
manifold point. Nondegeneracy is needed only for positive mass on nonempty
open sets. Neither symmetry nor a finite total mass is required.

No local finiteness, positivity, supplied measure, or chart measure identity
is an input. Compact finiteness uses the original Hausdorff hypothesis.
This is a measure on the base manifold, not the phase-space defect measure.
No Radon or arbitrary-atlas extension is asserted here.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ManifoldBilinear

namespace Burnett.Geometry.ManifoldVolumeRegularity
variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem coordinate_det_ne_zero (B : Field (M := M)) (hB : IsNondegenerate B)
    (c : M) {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    Matrix.det (metricComponents (coordinateBilinear B c) y) ≠ 0 := by
  have hn := coordinateBilinear_nondegenerate B hB c hy
  have hd := (LinearMap.BilinForm.nondegenerate_iff_det_ne_zero
    (B := coordinateBilinear B c y) coordinateBasis).mp hn
  have hm : BilinForm.toMatrix coordinateBasis (coordinateBilinear B c y) =
      metricComponents (coordinateBilinear B c) y := by
    ext i j
    simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
  simpa only [hm] using hd

theorem coordinateMeasure_compact_lt_top (B : Field (M := M)) (hB : IsSmooth B)
    (c : M) {K : Set CoordinateSpace} (hK : IsCompact K)
    (hKt : K ⊆ (chartAt CoordinateSpace c).target) :
    ManifoldVolume.coordinateMeasure B c K < ⊤ := by
  let q : CoordinateSpace → NNReal := fun y =>
    (Real.sqrt |Matrix.det (metricComponents (coordinateBilinear B c) y)|).toNNReal
  have hd : ContinuousOn (fun y => Matrix.det
      (metricComponents (coordinateBilinear B c) y)) K := by
    intro y hy
    exact continuous_id.matrix_det.continuousAt.comp_continuousWithinAt
      ((continuousOn_components B hB c).mono hKt y hy)
  have hq : ContinuousOn q K := continuous_real_toNNReal.comp_continuousOn hd.abs.sqrt
  change (volume.withDensity fun y => (q y : ENNReal)) K < ⊤
  rw [withDensity_apply _ hK.measurableSet]
  exact setLIntegral_lt_top_of_bddAbove hK.measure_lt_top.ne (hK.bddAbove_image hq)

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

theorem geometricMeasure_apply_of_subset_chart (B : Field (M := M)) (c : M)
    {V : Set M} (hV : MeasurableSet V) (hVs : V ⊆ (chartAt CoordinateSpace c).source) :
    ManifoldVolume.geometricMeasure B V =
      ManifoldVolume.coordinateMeasure B c ((chartAt CoordinateSpace c) '' V) := by
  let e := chartAt CoordinateSpace c
  have hre : (ManifoldVolume.geometricMeasure B) V =
      ((ManifoldVolume.geometricMeasure B).restrict e.source) V := by
    rw [Measure.restrict_apply hV, inter_eq_left.mpr hVs]
  rw [hre, ManifoldVolume.geometricMeasure_restrict]
  change (Measure.map (ManifoldVolume.inverseChart c)
    ((ManifoldVolume.coordinateMeasure B c).restrict e.target)) V = _
  rw [Measure.map_apply (ManifoldVolume.measurable_inverseChart c) hV,
    Measure.restrict_apply ((ManifoldVolume.measurable_inverseChart c) hV)]
  congr 1
  ext y
  constructor
  · rintro ⟨hv, hy⟩
    rw [mem_preimage, ManifoldVolume.inverseChart_of_mem c hy] at hv
    exact ⟨e.symm y, hv, e.right_inv hy⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨by simpa only [mem_preimage, ManifoldVolume.inverseChart_chart c (hVs hx)] using hx,
      e.mapsTo (hVs hx)⟩

theorem geometricMeasure_open_pos (B : Field (M := M)) (hs : IsSmooth B)
    (hn : IsNondegenerate B) {V : Set M} (hV : IsOpen V) (hne : V.Nonempty) :
    0 < ManifoldVolume.geometricMeasure B V := by
  obtain ⟨x, hx⟩ := hne
  let e := chartAt CoordinateSpace x
  let W := V ∩ e.source
  have hW : IsOpen W := hV.inter e.open_source
  have hWs : W ⊆ e.source := inter_subset_right
  have hWne : W.Nonempty := ⟨x, hx, mem_chart_source CoordinateSpace x⟩
  have himg : IsOpen (e '' W) := e.isOpen_image_of_subset_source hW hWs
  have hpos : 0 < ManifoldVolume.coordinateMeasure B x (e '' W) := by
    apply LorentzVolume.coordinateMeasure_open_pos _ e.target e.open_target
      (continuousOn_components B hs x) (fun y hy => coordinate_det_ne_zero B hn x hy)
      himg (hWne.image e)
    exact image_subset_iff.mpr (e.mapsTo.mono_left hWs)
  rw [← geometricMeasure_apply_of_subset_chart B x hW.measurableSet hWs] at hpos
  exact lt_of_lt_of_le hpos (measure_mono inter_subset_left)

theorem geometricMeasure_isOpenPosMeasure (B : Field (M := M))
    (hs : IsSmooth B) (hn : IsNondegenerate B) :
    (ManifoldVolume.geometricMeasure B).IsOpenPosMeasure :=
  ⟨fun _ hV hne => (geometricMeasure_open_pos B hs hn hV hne).ne'⟩

variable [T2Space M]

theorem geometricMeasure_isLocallyFiniteMeasure (B : Field (M := M))
    (hs : IsSmooth B) : IsLocallyFiniteMeasure (ManifoldVolume.geometricMeasure B) := by
  refine ⟨fun x => ?_⟩
  let e := chartAt CoordinateSpace x
  have hx : x ∈ e.source := mem_chart_source CoordinateSpace x
  obtain ⟨K, hK, hxK, hKt⟩ := exists_compact_subset e.open_target (e.mapsTo hx)
  have hKi : K ∈ 𝓝 (e x) := mem_interior_iff_mem_nhds.mp hxK
  have hUc : IsCompact (e.symm '' K) := hK.image_of_continuousOn (e.continuousOn_symm.mono hKt)
  have hUs : e.symm '' K ⊆ e.source := image_subset_iff.mpr (e.symm_mapsTo.mono_left hKt)
  have heK : e '' (e.symm '' K) = K := by
    ext y
    constructor
    · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
      simpa only [e.right_inv (hKt hw)] using hw
    · intro hy
      exact ⟨e.symm y, ⟨y, hy, rfl⟩, e.right_inv (hKt hy)⟩
  refine ⟨e.symm '' K, ?_, ?_⟩
  · simpa only [e.left_inv hx] using e.symm.image_mem_nhds (e.mapsTo hx) hKi
  · rw [geometricMeasure_apply_of_subset_chart B x hUc.measurableSet hUs, heK]
    exact coordinateMeasure_compact_lt_top B hs x hK hKt

theorem geometricMeasure_compact_lt_top (B : Field (M := M)) (hs : IsSmooth B)
    {K : Set M} (hK : IsCompact K) : ManifoldVolume.geometricMeasure B K < ⊤ := by
  letI := geometricMeasure_isLocallyFiniteMeasure B hs
  exact hK.measure_lt_top

end Burnett.Geometry.ManifoldVolumeRegularity
