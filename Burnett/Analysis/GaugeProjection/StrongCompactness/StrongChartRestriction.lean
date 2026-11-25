import Burnett.Analysis.GaugeProjection.StrongCompactness.StrongOpenSet

/-! The strong criterion with the manuscript's quantifier over charts in the open region. -/
set_option autoImplicit false
set_option maxRecDepth 3900
set_option maxHeartbeats 3300000

noncomputable section
namespace Burnett.P01

open Set Filter Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

local notation "E" => CoordinateSpace

/-- Testing a cutoff supported in the open region is the same as testing its
unchanged zero extension in the restricted maximal-atlas chart. -/
theorem hasStrongProjectedGradientOn_iff_all_charts_in_open
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (U : Set M) (hU : IsOpen U) :
    HasStrongProjectedGradientOn B g hB hg U ↔
      ∀ (c : AtlasChart M), c.chart.source ⊆ U → ∀ (χ : D)
        (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target),
        Tendsto (receivingStrongProjectionEnergy B g hB hg c χ hχ) atTop (𝓝 0) := by
  constructor
  · intro h c hc χ hχ
    apply h c χ hχ
    rintro _ ⟨y, hy, rfl⟩
    exact hc (c.chart.symm.mapsTo (hχ hy))
  · intro h c χ hχ hSupport
    let c' : AtlasChart M := ⟨c.chart.restr U,
      restr_mem_maximalAtlas (contDiffGroupoid ∞ Model) c.compatible hU⟩
    have hc' : c'.chart.source ⊆ U := by
      change (c.chart.restr U).source ⊆ U
      rw [c.chart.restr_source' U hU]
      exact inter_subset_right
    have hχ' : tsupport (χ : E → ℝ) ⊆ c'.chart.target := by
      change tsupport (χ : E → ℝ) ⊆ (c.chart.restr U).target
      rw [c.chart.restr_target, hU.interior_eq]
      exact fun y hy => ⟨hχ hy, hSupport ⟨y, hy, rfl⟩⟩
    have hEq : receivingCutoffFluctuation B g hB hg c' χ hχ' =
        receivingCutoffFluctuation B g hB hg c χ hχ := by
      funext n i j
      ext x
      rfl
    have hConv := h c' hc' χ hχ'
    simpa only [receivingStrongProjectionEnergy, hEq] using hConv

end Burnett.P01
