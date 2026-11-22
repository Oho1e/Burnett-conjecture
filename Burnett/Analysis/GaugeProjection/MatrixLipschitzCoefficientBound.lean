import Burnett.Analysis.GaugeProjection.MatrixAllSchwartzBound
import Burnett.Analysis.GaugeProjection.CoefficientProductLimit

set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.P01

open Filter
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff NNReal Topology

/-- Actual full matrix commutator on a differentiated Schwartz input, with
globally Lipschitz coefficients allowed to grow linearly. The two products
are the physical pointwise products as elements of \(L^2\). -/
def projectionLipschitzCommutatorL2 (b : Fin 4) (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (w : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
  let d := projectionMatrixDerivative b w
  projectionFullL2 (fun i j => projectionLipschitzCoefficientProductL2 f L hL (d i j)) -
    (fun i j => projectionLipschitzCoefficientProductL2 f L hL (projectionFullSchwartz d i j))

private theorem projectionLipschitzCommutatorL2_normalized (b : Fin 4) (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (w : ProjectionSchwartzMatrix) :
    projectionLipschitzCommutatorL2 b f L hL w =
      let d := projectionMatrixDerivative b w
      projectionFullL2 (fun i j => projectionNormalizedCoefficientProductL2 f L hL (d i j)) -
        (fun i j => projectionNormalizedCoefficientProductL2 f L hL (projectionFullSchwartz d i j)) := by
  let d := projectionMatrixDerivative b w
  let V (u : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
    fun i j => projectionNormalizedCoefficientProductL2 f L hL (u i j)
  change projectionFullL2 (V d + f 0 • projectionMatrixToL2 d) -
    (V (projectionFullSchwartz d) + f 0 • projectionMatrixToL2 (projectionFullSchwartz d)) =
      projectionFullL2 (V d) - V (projectionFullSchwartz d)
  rw [map_add, map_smul, projectionFullL2_eq_schwartz]
  abel

/-- The original projected-source commutator estimate on Schwartz matrix
fields and smooth globally Lipschitz coefficients. No bound on the size of
the coefficient or its higher derivatives enters the estimate. -/
theorem exists_projectionLipschitzCommutatorL2_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (b : Fin 4) (f : E → ℂ) (_hf : ContDiff ℝ ∞ f) (L : ℝ≥0) (hL : LipschitzWith L f)
        (w : ProjectionSchwartzMatrix),
        ‖projectionLipschitzCommutatorL2 b f L hL w‖ ≤ C * (L : ℝ) * ‖projectionMatrixToL2 w‖ := by
  obtain ⟨C, hC, est⟩ := exists_projectionFullCommutatorL2_bound
  let S := projectionCoefficientCutoffConstant
  refine ⟨C * (S : ℝ), by positivity, fun b f hf L hL w => ?_⟩
  let d := projectionMatrixDerivative b w
  let fn := projectionCoefficientCutoff f hf
  let A (u : ProjectionSchwartzMatrix) : ProjectionL2Matrix :=
    fun i j => projectionNormalizedCoefficientProductL2 f L hL (u i j)
  have hm (u : ProjectionSchwartzMatrix) :
      Tendsto (fun n => projectionMultiplyL2 (fn n) (projectionMatrixToL2 u)) atTop (𝓝 (A u)) := by
    apply tendsto_pi_nhds.2
    intro i
    apply tendsto_pi_nhds.2
    intro j
    simp only [projectionMultiplyL2_apply, projectionMatrixToL2, projectionMultiplyL2Scalar_schwartz]
    exact projectionCoefficientCutoff_product_tendsto f hf L hL (u i j)
  have ha := projectionFullL2.continuous.continuousAt.tendsto.comp (hm d)
  have hb := hm (projectionFullSchwartz d)
  have hsub := ha.sub hb
  have he (n : ℕ) :
      projectionFullL2 (projectionMultiplyL2 (fn n) (projectionMatrixToL2 d)) -
        projectionMultiplyL2 (fn n) (projectionMatrixToL2 (projectionFullSchwartz d)) =
      projectionFullCommutatorL2 b (fn n) w := by
    rw [← projectionFullL2_eq_schwartz]
    rfl
  have ht : Tendsto (fun n => projectionFullCommutatorL2 b (fn n) w)
      atTop (𝓝 (projectionLipschitzCommutatorL2 b f L hL w)) := by
    rw [projectionLipschitzCommutatorL2_normalized]
    simpa only [Function.comp_apply, he] using hsub
  apply le_of_tendsto' ht.norm
  intro n
  have hLn : LipschitzWith (S * L) (fn n) := projectionCoefficientCutoff_lipschitz f hf L hL n
  simpa only [NNReal.coe_mul, mul_assoc] using est b (fn n) (S * L) hLn w

end Burnett.P01
