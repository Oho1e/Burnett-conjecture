import Burnett.Analysis.Microlocal.PhysicalChartCover

set_option autoImplicit false

noncomputable section
namespace Burnett.Microlocal.CountableAuxiliaryCharts.CompactChartInput

open Set
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.X02.SobolevTestJet (test_smooth)
open scoped Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- A compact base window on which the inverse cutoff is uniformly bounded. -/
def compactCutoffLocus (q : CompactChartInput M) (δ : ℝ) : Set M :=
  (chartAt CoordinateSpace q.center).symm ''
    (q.ball.closedBall ∩ {y | δ ≤ ‖(q.cutoff : CoordinateSpace → ℝ) y‖})

theorem isCompact_compactCutoffLocus (q : CompactChartInput M) (δ : ℝ) :
    IsCompact (compactCutoffLocus q δ) := by
  have hClosed : IsClosed {y | δ ≤ ‖(q.cutoff : CoordinateSpace → ℝ) y‖} :=
    isClosed_le continuous_const (test_smooth q.cutoff).continuous.norm
  have hBall : IsCompact q.ball.closedBall := isCompact_closedBall _ _
  exact (hBall.inter_right hClosed).image_of_continuousOn
    ((chartAt CoordinateSpace q.center).continuousOn_symm.mono (inter_subset_left.trans q.ball_in_chart))

theorem mem_compactCutoffLocus (q : CompactChartInput M) {δ : ℝ} (hδ : 0 < δ) {x : M} :
    x ∈ compactCutoffLocus q δ ↔
      x ∈ (chartAt CoordinateSpace q.center).source ∧
      δ ≤ ‖(q.cutoff : CoordinateSpace → ℝ) (chartAt CoordinateSpace q.center x)‖ := by
  let e := chartAt CoordinateSpace q.center
  constructor
  · rintro ⟨y, ⟨hy, hχ⟩, rfl⟩
    have ht : y ∈ e.target := q.ball_in_chart hy
    refine ⟨e.symm_mapsTo ht, ?_⟩
    change δ ≤ ‖(q.cutoff : CoordinateSpace → ℝ) (e (e.symm y))‖
    rwa [e.right_inv ht]
  · rintro ⟨hx, hχ⟩
    have hBall : e x ∈ q.ball.closedBall :=
      q.cutoff_support (subset_tsupport _ (norm_pos_iff.mp (hδ.trans_le hχ)))
    exact ⟨e x, ⟨hBall, hχ⟩, e.left_inv hx⟩

theorem cutoffLocusAbove_subset_compactCutoffLocus (q : CompactChartInput M) {δ : ℝ}
    (hδ : 0 < δ) : q.cutoffLocusAbove δ ⊆ compactCutoffLocus q δ :=
  fun _ hx => (mem_compactCutoffLocus q hδ).mpr ⟨hx.1, hx.2.le⟩

theorem compactCutoffLocus_subset_nonzeroLocus (q : CompactChartInput M) {δ : ℝ}
    (hδ : 0 < δ) : compactCutoffLocus q δ ⊆ q.nonzeroLocus := by
  intro x hx
  obtain ⟨hSrc, hχ⟩ := (mem_compactCutoffLocus q hδ).mp hx
  exact ⟨hSrc, norm_pos_iff.mp (hδ.trans_le hχ)⟩

end Burnett.Microlocal.CountableAuxiliaryCharts.CompactChartInput
