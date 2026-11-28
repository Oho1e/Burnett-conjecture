import Burnett.Analysis.TransportWard.Weyl.OriginalF07NestedTestWindows
import Burnett.Analysis.Sobolev.TestJet

set_option autoImplicit false

noncomputable section
namespace Burnett.V03.Palatini

open Set Filter Bundle Burnett.Geometry
open ConnectionDifference (CoordinateSpace)
open ManifoldMetric (Model)
open MaximalChart (AtlasChart)
open CotangentAngularExtension (puncturedCotangent)
open UnitNullCompactness (CotangentBundle)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.X02.SobolevTestJet (D)
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The original F07 windows, expressed in the cutoff and neighborhood
types consumed by the actual localized Weyl test. -/
theorem exists_originalF07NestedWeylWindows
    (q : CompactChartInput M) (b : CotangentBundle M → ℝ)
    (S : Set M) (hS : IsCompact S) (hThreshold : S ⊆ q.cutoffLocusAbove (1 / 2))
    (hSupport : ∀ p ∈ puncturedCotangent, p.proj ∉ S → b p = 0) :
    let c := AtlasChart.atPoint q.center
    ∃ (K : Set M) (L : Set CoordinateSpace) (χ : D) (θ : SchwartzMap CoordinateSpace ℝ),
      IsCompact K ∧ S ⊆ K ∧ K ⊆ q.cutoffLocusAbove (1 / 2) ∧ K ⊆ q.nonzeroLocus ∧
      L = c.chart '' S ∧ IsCompact L ∧ L ⊆ (chartAt CoordinateSpace q.center).target ∧
      tsupport (χ : CoordinateSpace → ℝ) ⊆ c.chart '' K ∧
      Continuous (θ : CoordinateSpace → ℝ) ∧ HasCompactSupport (θ : CoordinateSpace → ℝ) ∧
      (∀ x ∈ L, θ x = 1) ∧
      (∀ x ∈ tsupport (θ : CoordinateSpace → ℝ),
        (χ : CoordinateSpace → ℝ) =ᶠ[𝓝 x] fun _ : CoordinateSpace => (1 : ℝ)) ∧
      ∀ p ∈ puncturedCotangent, b p ≠ 0 →
        p.proj ∈ K ∧ c.chart p.proj ∈ L ∧ θ (c.chart p.proj) = 1 ∧
        (χ : CoordinateSpace → ℝ) (c.chart p.proj) = 1 := by
  intro c
  obtain ⟨K, L, V, χ₀, θ, hK, hSK, hKThreshold, hKNonzero, hLOri, hL, hLTarget,
    hχCompact, hθCompact, hθL, hV, hθV, hχV, _, hχK, hb⟩ :=
    exists_originalF07NestedTestWindows q b S hS hThreshold hSupport
  let χ : D := ⟨(χ₀ : CoordinateSpace → ℝ), ⟨χ₀.smooth', hχCompact⟩⟩
  have hχθ (x : CoordinateSpace) (hx : x ∈ tsupport (θ : CoordinateSpace → ℝ)) :
      (χ : CoordinateSpace → ℝ) =ᶠ[𝓝 x] fun _ : CoordinateSpace => (1 : ℝ) := by
    filter_upwards [hV.mem_nhds (hθV hx)] with y hy
    exact hχV hy
  exact ⟨K, L, χ, θ, hK, hSK, hKThreshold, hKNonzero, hLOri, hL, hLTarget,
    hχK.le, θ.smooth'.continuous, hθCompact, fun _ hx => hθL hx, hχθ, hb⟩

end Burnett.V03.Palatini
