import Burnett.Analysis.TransportWard.Weyl.OriginalF07NestedWeylWindows

set_option autoImplicit false
set_option maxHeartbeats 4300000

noncomputable section

namespace Burnett.V03.Palatini

open Filter Metric Set Burnett.Geometry ConnectionDifference
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.X02.SobolevTestJet (D test_smooth)
open scoped ContDiff Manifold Topology

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- The actual output window can be covered by the existing cubic patch
family inside the same represented coordinate ball. All sufficiently small
outer patches are contained where the input localization equals one. -/
theorem exists_originalF07WeylPatchWindow
    (q : CompactChartInput M) (K : Set M) (hK : K ⊆ q.nonzeroLocus)
    (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ (chartAt E q.center) '' K)
    (θ : E → ℝ) (hθ : HasCompactSupport θ)
    (hPlateau : ∀ x ∈ tsupport θ, (χ : E → ℝ) =ᶠ[𝓝 x] fun _ : E => (1 : ℝ)) :
    let V := q.ball.closedBall
    ∃ Kplus : Set E, IsCompact Kplus ∧ tsupport θ ⊆ interior Kplus ∧
      Kplus ⊆ V ∧ IsCompact V ∧ Convex ℝ V ∧ V ⊆ (chartAt E q.center).target ∧
      ∀ x ∈ Kplus, (χ : E → ℝ) x = 1 := by
  intro V
  let NZ := {x : E | (q.cutoff : E → ℝ) x ≠ 0}
  have hNZ : IsOpen NZ := isOpen_ne_fun (test_smooth q.cutoff).continuous continuous_const
  have hNZV : NZ ⊆ V := fun _ hx => q.cutoff_support (subset_tsupport (q.cutoff : E → ℝ) hx)
  have hToNZ : tsupport (χ : E → ℝ) ⊆ NZ := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hχ hx
    exact (hK hy).2
  let U := NZ ∩ interior {x : E | (χ : E → ℝ) x = 1}
  have hU : IsOpen U := hNZ.inter isOpen_interior
  have hθU : tsupport θ ⊆ U := by
    intro x hx
    have he := hPlateau x hx
    have hOne : (χ : E → ℝ) x = 1 := he.self_of_nhds
    have hχx : x ∈ tsupport (χ : E → ℝ) := subset_tsupport _ (by
      change (χ : E → ℝ) x ≠ 0
      rw [hOne]
      exact one_ne_zero)
    exact ⟨hToNZ hχx, mem_interior_iff_mem_nhds.mpr he⟩
  obtain ⟨s, hs, hClose⟩ := hθ.isCompact.exists_cthickening_subset_open hU hθU
  let S := Metric.cthickening s (tsupport θ)
  have hInner : tsupport θ ⊆ interior S :=
    (self_subset_thickening hs _).trans
      (interior_maximal (thickening_subset_cthickening s _) isOpen_thickening)
  have hV : IsCompact V := isCompact_closedBall q.ball.center q.ball.radius
  have hVC : Convex ℝ V := convex_closedBall q.ball.center q.ball.radius
  refine ⟨S, hθ.isCompact.cthickening, hInner, hClose.trans (inter_subset_left.trans hNZV),
    hV, hVC, q.ball_in_chart, ?_⟩
  intro x hx
  have hχx : x ∈ {y : E | (χ : E → ℝ) y = 1} := interior_subset (hClose hx).2
  exact hχx

end Burnett.V03.Palatini
