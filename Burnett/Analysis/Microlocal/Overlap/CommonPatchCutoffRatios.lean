import Burnett.Analysis.Microlocal.Overlap.CommonPatchInputs

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapWindows.CommonCutoffPatch

open Set
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable {q d : CompactChartInput M} {x : CoordinateSpace}
variable (p : CommonCutoffPatch q.center d.center q.ball.closedBall d.ball.closedBall q.cutoff d.cutoff x)

theorem source_mem_halfBall_of_mapped_mem_targetPlateau {y : CoordinateSpace}
    (hy : y ∈ p.sourceInput.ball.closedBall)
    (hTy : chartTransition q.center d.center y ∈ p.targetPlateau) :
    y ∈ Metric.closedBall x (p.sourceRadius / 2) := by
  obtain ⟨z, hz, he⟩ := hTy
  have hsub : Metric.closedBall x (p.sourceRadius / 2) ⊆ p.sourceInput.ball.closedBall :=
    Metric.closedBall_subset_closedBall (show p.sourceRadius / 2 ≤ p.sourceRadius by
      linarith [p.sourceRadius_pos])
  change chartTransition q.center d.center z = chartTransition q.center d.center y at he
  have hzy := (chartTransition q.center d.center).injOn
    (p.sourceInput_ball_in_overlap (hsub hz)) (p.sourceInput_ball_in_overlap hy) he
  exact hzy ▸ hz

/-- The source reweighting factor is the reciprocal of the original cutoff
on the source plateau. -/
theorem sourceFactor_on_halfBall {y : CoordinateSpace} (hy : y ∈ Metric.closedBall x (p.sourceRadius / 2)) :
    (p.sourceFactor : CoordinateSpace → ℝ) y = ((q.cutoff : CoordinateSpace → ℝ) y)⁻¹ := by
  have hsub : Metric.closedBall x (p.sourceRadius / 2) ⊆ Metric.closedBall x p.sourceRadius :=
    Metric.closedBall_subset_closedBall (by linarith [p.sourceRadius_pos])
  have hq : (q.cutoff : CoordinateSpace → ℝ) y ≠ 0 := (p.sourceWindow (hsub hy)).2.2
  rw [← one_div]
  exact (eq_div_iff hq).2 ((p.sourceCutoff_eq_mul y).symm.trans (p.sourceCutoff_one y hy))

/-- The target reweighting factor is the reciprocal of the original cutoff
on the transported plateau. -/
theorem targetFactor_on_targetPlateau {y : CoordinateSpace} (hy : y ∈ p.targetPlateau) :
    (p.targetFactor : CoordinateSpace → ℝ) y = ((d.cutoff : CoordinateSpace → ℝ) y)⁻¹ := by
  have hd : (d.cutoff : CoordinateSpace → ℝ) y ≠ 0 :=
    (p.targetWindow (Metric.ball_subset_closedBall (p.targetPlateau_subset_targetBall hy))).2.2
  rw [← one_div]
  exact (eq_div_iff hd).2 ((p.targetCutoff_eq_mul y).symm.trans (p.targetInput_cutoff_one_on_targetPlateau y hy))

end Burnett.Microlocal.OverlapWindows.CommonCutoffPatch
