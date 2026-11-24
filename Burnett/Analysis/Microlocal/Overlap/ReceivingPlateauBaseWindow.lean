import Burnett.Analysis.Microlocal.Overlap.ReceivingRepresentedSquarePartition
import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitude

/-! Compact manifold witnesses for the coordinate windows of the square partition. -/

set_option autoImplicit false
set_option maxHeartbeats 600000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set Burnett.Geometry
open ConnectionDifference ManifoldMetric MaximalChart
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open scoped Manifold ContDiff Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The closed represented source plateau gives a compact base set in the
receiving chart. Its image agrees with the true overlap image. -/
theorem represented_closedPlateau_baseWindow (q : CompactChartInput M) (c : AtlasChart M)
    (δ : ℝ) (hδ : δ ≤ q.ball.radius)
    (hOuter : q.ball.closedBall ⊆ ((AtlasChart.atPoint q.center).transition c).source)
    (hOne : ∀ y ∈ Metric.closedBall q.ball.center δ, (q.cutoff : E → ℝ) y = 1) :
    let e := chartAt E q.center
    let S := Metric.closedBall q.ball.center δ
    let K := e.symm '' S
    IsCompact K ∧ K ⊆ q.nonzeroLocus ∩ c.chart.source ∧
      c.chart '' K = (AtlasChart.atPoint q.center).transition c '' S := by
  intro e S K
  let t := (AtlasChart.atPoint q.center).transition c
  have hOuter' : S ⊆ t.source := (Metric.closedBall_subset_closedBall hδ).trans hOuter
  have hS : S ⊆ e.target := fun _ hx => (hOuter' hx).1
  refine ⟨(isCompact_closedBall _ _).image_of_continuousOn (e.continuousOn_symm.mono hS), ?_, ?_⟩
  · rintro _ ⟨y, hy, rfl⟩
    refine ⟨⟨e.symm_mapsTo (hS hy), ?_⟩, (hOuter' hy).2⟩
    change (q.cutoff : E → ℝ) (e (e.symm y)) ≠ 0
    rw [e.right_inv (hS hy), hOne y hy]
    exact one_ne_zero
  · rw [Set.image_image]
    rfl

end Burnett.Microlocal.Overlap
