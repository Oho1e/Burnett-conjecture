import Burnett.Analysis.GaugeProjection.MatrixAnnularBound
import Burnett.Analysis.GaugeProjection.MatrixAnnularApproximation

set_option autoImplicit false
set_option maxHeartbeats 2000000

noncomputable section

namespace Burnett.P01

open Filter
open Burnett.A02.FrequencySplit (E)
open scoped NNReal Topology

/-- Removal of the common spectrum restriction, keeping exactly the two Hodge
slots, the fixed low-frequency profile, the differentiated field and the same
commutator constant. -/
theorem exists_projectionFullCommutatorL2_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Fin 4) (f : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L (f : E → ℂ) →
        ∀ (w : ProjectionSchwartzMatrix),
          ‖projectionFullCommutatorL2 b f w‖ ≤ C * (L : ℝ) * ‖projectionMatrixToL2 w‖ := by
  obtain ⟨C, hC, est⟩ := exists_projectionFullCommutatorL2_bound_on_annularCore
  refine ⟨C, hC, fun b f L hf w => ?_⟩
  let v := projectionMatrixAnnularApproximation w
  let M := projectionMultiplyL2 f
  let A : ProjectionL2Matrix →L[ℂ] ProjectionL2Matrix :=
    projectionFullL2.comp M - M.comp projectionFullL2
  have hw := (projectionMatrixAnnularApproximation_tendsto w).norm
  have hd := projectionMatrixAnnularApproximation_derivative_tendsto b w
  have ha : Tendsto (fun n => projectionFullCommutatorL2 b f (v n)) atTop
      (𝓝 (projectionFullCommutatorL2 b f w)) := A.continuous.continuousAt.tendsto.comp hd
  apply le_of_tendsto_of_tendsto' ha.norm (tendsto_const_nhds.mul hw)
  intro n
  obtain ⟨K, hK, h0, hS⟩ := projectionMatrixAnnularApproximation_compact w n
  exact est b f L hf (v n) K hK h0 hS

end Burnett.P01
