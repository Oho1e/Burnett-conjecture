import Burnett.Analysis.Microlocal.PhysicalChartCover
import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives
import Burnett.Geometry.MaximalChart.MetricCoordinates
import Burnett.Geometry.Cotangent.SmoothExtension

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.V03.Palatini

open Set Bundle Burnett.Geometry
open ConnectionDifference (CoordinateSpace)
open ManifoldMetric (Model)
open MaximalChart (AtlasChart)
open CotangentAngularExtension (puncturedCotangent)
open UnitNullCompactness (CotangentBundle)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.P01 (exists_projectedChartCutoff)
open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The original F07 chart and the compact base support of the same
cotangent test give nested real Schwartz cutoffs. The outer support pulls
back to a compact set in the original cutoff's positive threshold region. -/
theorem exists_originalF07NestedTestWindows
    (q : CompactChartInput M) (b : CotangentBundle M → ℝ)
    (S : Set M) (hS : IsCompact S) (hThreshold : S ⊆ q.cutoffLocusAbove (1 / 2))
    (hSupport : ∀ p ∈ puncturedCotangent, p.proj ∉ S → b p = 0) :
    let c := AtlasChart.atPoint q.center
    ∃ (K : Set M) (L V : Set CoordinateSpace) (χ θ : SchwartzMap CoordinateSpace ℝ),
      IsCompact K ∧ S ⊆ K ∧ K ⊆ q.cutoffLocusAbove (1 / 2) ∧ K ⊆ q.nonzeroLocus ∧
      L = c.chart '' S ∧ IsCompact L ∧ L ⊆ c.chart.target ∧
      HasCompactSupport (χ : CoordinateSpace → ℝ) ∧ HasCompactSupport (θ : CoordinateSpace → ℝ) ∧
      EqOn (θ : CoordinateSpace → ℝ) 1 L ∧ IsOpen V ∧
      tsupport (θ : CoordinateSpace → ℝ) ⊆ V ∧ EqOn (χ : CoordinateSpace → ℝ) 1 V ∧
      V ⊆ c.chart '' K ∧ tsupport (χ : CoordinateSpace → ℝ) = c.chart '' K ∧
      ∀ p ∈ puncturedCotangent, b p ≠ 0 →
        p.proj ∈ K ∧ c.chart p.proj ∈ L ∧ θ (c.chart p.proj) = 1 ∧ χ (c.chart p.proj) = 1 := by
  classical
  intro c
  let U := c.chart '' q.cutoffLocusAbove (1 / 2)
  let L := c.chart '' S
  have hSource : q.cutoffLocusAbove (1 / 2) ⊆ c.chart.source := fun _ hx => hx.1
  have hU : IsOpen U :=
    c.chart.isOpen_image_of_subset_source (q.isOpen_cutoffLocusAbove (1 / 2)) hSource
  have hUTarget : U ⊆ c.chart.target := by
    rintro y ⟨x, hx, rfl⟩
    exact c.chart.map_source (hSource hx)
  have hL : IsCompact L :=
    hS.image_of_continuousOn (c.chart.continuousOn.mono (hThreshold.trans hSource))
  have hLU : L ⊆ U := image_mono hThreshold
  obtain ⟨θ₀, hθDiff, hθCompact, hθU, W, _, hLW, _, hθW⟩ :=
    exists_projectedChartCutoff hL hU hLU
  obtain ⟨χ₀, hχDiff, hχCompact, hχU, V, hV, hθV, _, hχV⟩ :=
    exists_projectedChartCutoff hθCompact hU hθU
  let θ := hθCompact.toSchwartzMap hθDiff
  let χ := hχCompact.toSchwartzMap hχDiff
  let K := c.chart.symm '' tsupport χ₀
  have hK : IsCompact K :=
    hχCompact.image_of_continuousOn (c.chart.continuousOn_symm.mono (hχU.trans hUTarget))
  have hKThreshold : K ⊆ q.cutoffLocusAbove (1 / 2) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hχU hx
    rw [c.chart.left_inv (hSource hz)]
    exact hz
  have hImage : c.chart '' K = tsupport χ₀ := by
    apply Subset.antisymm
    · rintro y ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      rw [c.chart.right_inv (hUTarget (hχU hz))]
      exact hz
    · intro y hy
      exact ⟨c.chart.symm y, ⟨y, hy, rfl⟩, c.chart.right_inv (hUTarget (hχU hy))⟩
  have hLθ : L ⊆ tsupport θ₀ := by
    intro y hy
    have eq : θ₀ y = 1 := hθW (hLW hy)
    exact subset_tsupport _ (show θ₀ y ≠ 0 by simpa only [eq] using (one_ne_zero : (1 : ℝ) ≠ 0))
  have hVχ : V ⊆ tsupport χ₀ := by
    intro y hy
    have eq : χ₀ y = 1 := hχV hy
    exact subset_tsupport _ (show χ₀ y ≠ 0 by simpa only [eq] using (one_ne_zero : (1 : ℝ) ≠ 0))
  have hLV : L ⊆ V := hLθ.trans hθV
  have hSK : S ⊆ K := by
    intro x hx
    have hxL : c.chart x ∈ L := mem_image_of_mem _ hx
    exact ⟨c.chart x, hVχ (hLV hxL), c.chart.left_inv (hSource (hThreshold hx))⟩
  refine ⟨K, L, V, χ, θ, hK, hSK, hKThreshold,
    hKThreshold.trans (q.cutoffLocusAbove_subset_nonzeroLocus (by norm_num)), rfl, hL, hLU.trans hUTarget,
    hχCompact, hθCompact, fun _ hx => hθW (hLW hx), hV, hθV, hχV, ?_, hImage.symm, ?_⟩
  · rwa [hImage]
  intro p hp hNonzero
  have hpS : p.proj ∈ S := by
    by_contra hn
    exact hNonzero (hSupport p hp hn)
  have hpL : c.chart p.proj ∈ L := mem_image_of_mem _ hpS
  exact ⟨hSK hpS, hpL, hθW (hLW hpL), hχV (hLV hpL)⟩

end Burnett.V03.Palatini
