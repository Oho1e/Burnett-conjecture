import Burnett.Analysis.Microlocal.CompactChartInput
import Burnett.Geometry.FlatRigidity.WeakCurvature
import Mathlib.Topology.Compactness.Lindelof

/-! Countably many compact preferred-chart windows cover the base by open
sets on which the cutoff reweighting is bounded. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Set MeasureTheory
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.FlatRigidity (exists_smooth_cutoff_on_compact_chart)
open Burnett.X02.SobolevTestJet (test_smooth)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

namespace CompactChartInput

/-- The open subset of the base where this chart's actual cutoff is nonzero. -/
def nonzeroLocus (q : CompactChartInput M) : Set M :=
  let e := chartAt CoordinateSpace q.center
  e.source ∩ e ⁻¹' Function.support (q.cutoff : CoordinateSpace → ℝ)

private theorem isOpen_cutoffSupport (q : CompactChartInput M) :
    IsOpen (Function.support (q.cutoff : CoordinateSpace → ℝ)) :=
  (isClosed_eq (test_smooth q.cutoff).continuous continuous_const).isOpen_compl

theorem isOpen_nonzeroLocus (q : CompactChartInput M) : IsOpen q.nonzeroLocus :=
  (chartAt CoordinateSpace q.center).isOpen_inter_preimage q.isOpen_cutoffSupport

/-- A nonzero cutoff places the coordinate point in the interior of the
actual closed window. -/
theorem chart_mem_interior_of_mem_nonzeroLocus (q : CompactChartInput M)
    {x : M} (hx : x ∈ q.nonzeroLocus) :
    chartAt CoordinateSpace q.center x ∈ interior q.ball.closedBall :=
  interior_maximal ((subset_tsupport (q.cutoff : CoordinateSpace → ℝ)).trans
    q.cutoff_support) q.isOpen_cutoffSupport hx.2

/-- The open part of the base where the magnitude of the cutoff exceeds `δ`. -/
def cutoffLocusAbove (q : CompactChartInput M) (δ : ℝ) : Set M :=
  let e := chartAt CoordinateSpace q.center
  e.source ∩ e ⁻¹' {y | δ < ‖(q.cutoff : CoordinateSpace → ℝ) y‖}

theorem cutoffLocusAbove_zero (q : CompactChartInput M) :
    q.cutoffLocusAbove 0 = q.nonzeroLocus := by
  ext x
  exact and_congr_right fun _ => norm_pos_iff

theorem isOpen_cutoffLocusAbove (q : CompactChartInput M) (δ : ℝ) :
    IsOpen (q.cutoffLocusAbove δ) :=
  (chartAt CoordinateSpace q.center).isOpen_inter_preimage
    (isOpen_lt continuous_const (test_smooth q.cutoff).continuous.norm)

theorem measurableSet_cutoffLocusAbove [MeasurableSpace M] [BorelSpace M]
    (q : CompactChartInput M) (δ : ℝ) : MeasurableSet (q.cutoffLocusAbove δ) :=
  (q.isOpen_cutoffLocusAbove δ).measurableSet

theorem cutoffLocusAbove_subset_nonzeroLocus (q : CompactChartInput M)
    {δ : ℝ} (hδ : 0 < δ) : q.cutoffLocusAbove δ ⊆ q.nonzeroLocus := by
  intro x hx
  exact ⟨hx.1, norm_pos_iff.mp (hδ.trans hx.2)⟩

theorem nonzeroLocus_eq_iUnion_cutoffLocusAbove (q : CompactChartInput M) :
    q.nonzeroLocus = ⋃ n : ℕ, q.cutoffLocusAbove (1 / (n + 1 : ℝ)) := by
  refine Subset.antisymm ?_ (iUnion_subset fun n =>
    q.cutoffLocusAbove_subset_nonzeroLocus (one_div_pos.mpr (by positivity)))
  intro x hx
  have hχ : (q.cutoff : CoordinateSpace → ℝ) (chartAt CoordinateSpace q.center x) ≠ 0 := hx.2
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (norm_pos_iff.mpr hχ)
  exact mem_iUnion.mpr ⟨n, hx.1, hn⟩

/-- On a positive threshold set the reciprocal cutoff square is bounded,
irrespective of the sign of the real cutoff. -/
theorem norm_inv_sq_le_of_mem_cutoffLocusAbove (q : CompactChartInput M)
    {δ : ℝ} (hδ : 0 < δ) {x : M} (hx : x ∈ q.cutoffLocusAbove δ) :
    ‖(((q.cutoff : CoordinateSpace → ℝ) (chartAt CoordinateSpace q.center x))⁻¹) ^ 2‖ ≤
      δ⁻¹ ^ 2 := by
  have hχ : δ < ‖(q.cutoff : CoordinateSpace → ℝ) (chartAt CoordinateSpace q.center x)‖ := hx.2
  rw [norm_pow, norm_inv]
  exact pow_le_pow_left₀ (inv_nonneg.mpr (norm_nonneg _)) (inv_anti₀ hδ hχ.le) 2

end CompactChartInput

/-- Each base point admits a compact window of its preferred chart with a
positive radius, and a smooth cutoff equal to one at that point. -/
theorem exists_centered_compactChartInput (x : M) :
    ∃ q : CompactChartInput M, q.center = x ∧
      q.ball.center = chartAt CoordinateSpace x x ∧ 0 < q.ball.radius ∧
      (q.cutoff : CoordinateSpace → ℝ) (chartAt CoordinateSpace q.center x) = 1 := by
  let e := chartAt CoordinateSpace x
  let y := e x
  have hy : y ∈ e.target := e.map_source (mem_chart_source CoordinateSpace x)
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds hy)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hBall : Metric.closedBall y r ⊆ e.target :=
    (Metric.closedBall_subset_ball (half_lt_self hε)).trans hεU
  have hCenter : {y} ⊆ Metric.ball y r :=
    singleton_subset_iff.mpr (Metric.mem_ball_self hr)
  obtain ⟨L, _, _, hLU, χ, hχSmooth, hχCompact, hχL, _, hχOne⟩ :=
    exists_smooth_cutoff_on_compact_chart isCompact_singleton Metric.isOpen_ball hCenter
  let q : CompactChartInput M := {
    center := x
    ball := ⟨y, r, hr.le⟩
    ball_in_chart := hBall
    cutoff := ⟨χ, hχSmooth, hχCompact⟩
    cutoff_support := hχL.trans (hLU.trans Metric.ball_subset_closedBall) }
  exact ⟨q, rfl, rfl, hr, hχOne y (mem_singleton y)⟩

/-- One countable family covers the manifold even with a common positive
cutoff threshold. Its full nonzero loci therefore also cover the base. -/
theorem exists_countable_compactChartInput_cover [SecondCountableTopology M] [Nonempty M] :
    ∃ q : ℕ → CompactChartInput M,
      (⋃ n, (q n).cutoffLocusAbove (1 / 2)) = (univ : Set M) ∧
      (⋃ n, (q n).nonzeroLocus) = (univ : Set M) := by
  classical
  choose p hCenter _ _ hOne using exists_centered_compactChartInput (M := M)
  have hHalf : (0 : ℝ) < 1 / 2 := by norm_num
  have hCover : (univ : Set M) ⊆ ⋃ x : M, (p x).cutoffLocusAbove (1 / 2) := by
    intro x _
    have hSource : x ∈ (chartAt CoordinateSpace (p x).center).source := by
      rw [hCenter x]
      exact mem_chart_source CoordinateSpace x
    refine mem_iUnion.mpr ⟨x, hSource, ?_⟩
    change (1 / 2 : ℝ) < ‖((p x).cutoff : CoordinateSpace → ℝ)
      (chartAt CoordinateSpace (p x).center x)‖
    rw [hOne x, norm_one]
    norm_num
  obtain ⟨a, ha⟩ := isLindelof_univ.indexed_countable_subcover
    (fun x : M => (p x).cutoffLocusAbove (1 / 2))
    (fun x => (p x).isOpen_cutoffLocusAbove (1 / 2)) hCover
  let q := p ∘ a
  refine ⟨q, eq_univ_of_univ_subset ha, eq_univ_of_univ_subset (ha.trans ?_)⟩
  exact iUnion_mono (fun n => (q n).cutoffLocusAbove_subset_nonzeroLocus hHalf)

end Burnett.Microlocal.CountableAuxiliaryCharts
