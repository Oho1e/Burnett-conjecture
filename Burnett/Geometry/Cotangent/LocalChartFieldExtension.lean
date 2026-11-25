import Mathlib.Analysis.Calculus.BumpFunction.Basic

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter Metric
open scoped ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [HasContDiffBump E]

/-- A smooth field on an open chart has a global smooth cutoff extension
that is exactly equal to the chart field on a neighborhood of the point. -/
theorem exists_smooth_chartField_extension {f : E → E} {V : Set E} {x : E}
    (hV : IsOpen V) (hx : x ∈ V) (hf : ContDiffOn ℝ ∞ f V) :
    ∃ W : Set E, IsOpen W ∧ x ∈ W ∧ W ⊆ V ∧
      ∃ F : E → E, ContDiff ℝ ∞ F ∧ EqOn F f W := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hV.mem_nhds hx)
  let cutoff : ContDiffBump x := ⟨r / 4, r / 2, by positivity, by linarith⟩
  let W := ball x cutoff.rIn
  let F (y : E) := cutoff y • f y
  have hW : W ⊆ V := (ball_subset_ball (by dsimp [cutoff]; linarith)).trans hball
  have hSupp : closedBall x cutoff.rOut ⊆ V :=
    (closedBall_subset_ball (by dsimp [cutoff]; linarith)).trans hball
  refine ⟨W, isOpen_ball, mem_ball_self cutoff.rIn_pos, hW, F, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ V
    · exact cutoff.contDiff.contDiffAt.smul (hf.contDiffAt (hV.mem_nhds hy))
    · have hu : y ∈ (closedBall x cutoff.rOut)ᶜ := fun h => hy (hSupp h)
      have hev : F =ᶠ[𝓝 y] (fun _ => (0 : E)) := by
        filter_upwards [isClosed_closedBall.isOpen_compl.mem_nhds hu] with z hz
        have hdist : cutoff.rOut ≤ dist z x := by
          have hn : ¬dist z x ≤ cutoff.rOut := hz
          exact (lt_of_not_ge hn).le
        simp [F, cutoff.zero_of_le_dist hdist]
      exact (contDiff_const : ContDiff ℝ ∞ (fun _ : E => (0 : E))).contDiffAt.congr_of_eventuallyEq hev
  · intro y hy
    simp [F, cutoff.one_of_mem_closedBall (ball_subset_closedBall hy)]

end Burnett.Geometry.CotangentHamiltonInitialFamily
