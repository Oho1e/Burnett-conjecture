import Burnett.Analysis.GaugeProjection.ProjectedDivergenceDefinitions
import Burnett.Analysis.GaugeProjection.ProjectedSchwartzIdentities

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.P01

open MeasureTheory
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open scoped BigOperators

/-- The actual commutator correction summed over the two coordinate indices. -/
def projectedSourceCommutatorSum (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) :
    ProjectionL2Matrix :=
  ∑ a, ∑ b, projectionLipschitzCommutatorL2 a (A.entry a b) A.slope
    (A.lipschitz a b) (projectionMatrixDerivative b z)

private theorem projectedSourceCommutatorSum_eq (A : ProjectedSourceCoefficients)
    (z : ProjectionSchwartzMatrix) :
    projectedSourceCommutatorSum A z =
      projectionFullL2 (projectedSourceQ A z) - projectedSourceQ A (projectionFullSchwartz z) := by
  let X (a b : Fin 4) : ProjectionL2Matrix := fun i j =>
    projectionLipschitzCoefficientProductL2 (A.entry a b) A.slope (A.lipschitz a b)
      (coordinateDerivative a (coordinateDerivative b (z i j)))
  let Y (a b : Fin 4) : ProjectionL2Matrix := fun i j =>
    projectionLipschitzCoefficientProductL2 (A.entry a b) A.slope (A.lipschitz a b)
      (coordinateDerivative a (coordinateDerivative b (projectionFullSchwartz z i j)))
  have h (a b : Fin 4) :
      projectionLipschitzCommutatorL2 a (A.entry a b) A.slope (A.lipschitz a b)
        (projectionMatrixDerivative b z) = projectionFullL2 (X a b) - Y a b := by
    dsimp only [projectionLipschitzCommutatorL2]
    rw [projectionFullSchwartz_coordinateDerivative, projectionFullSchwartz_coordinateDerivative]
    rfl
  unfold projectedSourceCommutatorSum
  simp_rw [h, Finset.sum_sub_distrib]
  change _ = projectionFullL2 (∑ a, ∑ b, X a b) - ∑ a, ∑ b, Y a b
  simp_rw [map_sum]

/-- The exact full-space equation of lines 1687–1689, in physical \(L^2\).
The left side represents the literal classical divergence at every component. -/
theorem projectedSourceDivergenceL2_eq_projected (A : ProjectedSourceCoefficients)
    (z : ProjectionSchwartzMatrix) :
    projectedSourceDivergenceL2 A (projectionFullSchwartz z) =
      -projectionFullL2 (projectedSourceQ A z) + projectedSourceCommutatorSum A z -
        projectedSourceCoefficientCorrection A (projectionFullSchwartz z) := by
  rw [projectedSourceDivergenceL2_eq_raw, projectedSourceCommutatorSum_eq]
  abel

/-- Sum of the \(L^2\) matrix norms of the four actual coordinate derivatives. -/
def projectedSourceGradientMass (z : ProjectionSchwartzMatrix) : ℝ :=
  ∑ b, ‖projectionMatrixToL2 (projectionMatrixDerivative b z)‖

private theorem matrixDoubleSum_norm_le (F : Fin 4 → Fin 4 → ProjectionL2Matrix)
    (m : ℝ) (B : Fin 4 → ℝ) (h : ∀ a b, ‖F a b‖ ≤ m * B b) :
    ‖∑ a, ∑ b, F a b‖ ≤ 4 * m * ∑ b, B b := by
  calc
    _ ≤ ∑ a : Fin 4, ‖∑ b, F a b‖ := norm_sum_le _ _
    _ ≤ ∑ a : Fin 4, ∑ b : Fin 4, ‖F a b‖ :=
      Finset.sum_le_sum fun a _ => norm_sum_le _ _
    _ ≤ ∑ _ : Fin 4, ∑ b : Fin 4, m * B b :=
      Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => h a b
    _ = _ := by
      simp only [← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
      ring

private theorem projectedSourceCoefficientCorrection_norm_le
    (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix) :
    ‖projectedSourceCoefficientCorrection A (projectionFullSchwartz z)‖ ≤
      4 * ((A.slope : ℝ) * ‖projectionFullL2‖) * projectedSourceGradientMass z := by
  let u := projectionFullSchwartz z
  unfold projectedSourceCoefficientCorrection projectedSourceGradientMass
  apply matrixDoubleSum_norm_le
  intro a b
  let W := projectionMatrixToL2 (projectionMatrixDerivative b z)
  let V := projectionMatrixToL2 (projectionMatrixDerivative b u)
  have hVW : V = projectionFullL2 W := by
    rw [projectionFullL2_eq_schwartz, projectionFullSchwartz_coordinateDerivative]
  have h : ‖V‖ ≤ ‖projectionFullL2‖ * ‖W‖ := hVW ▸ projectionFullL2.le_opNorm W
  have each :
      ‖fun i j => projectedSourceDerivativeProduct A a b ((coordinateDerivative b (u i j)).toLp 2 volume)‖
      ≤ (A.slope : ℝ) * ‖V‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro i
    apply (pi_norm_le_iff_of_nonneg (by positivity)).2
    intro j
    exact (projectedSourceDerivativeProduct_norm_le A a b (V i j)).trans
      (mul_le_mul_of_nonneg_left ((norm_le_pi_norm (V i) j).trans (norm_le_pi_norm V i)) A.slope.2)
  calc
    _ ≤ (A.slope : ℝ) * ‖V‖ := each
    _ ≤ (A.slope : ℝ) * (‖projectionFullL2‖ * ‖W‖) := mul_le_mul_of_nonneg_left h A.slope.2
    _ = _ := by ring

/-- The actual global projected divergence is bounded by the projected \(Q\)
term and the uniform first-order coefficient bound times the first derivatives
of the input. All constants are independent of the coefficient values. -/
theorem exists_projectedSourceDivergenceL2_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix),
      ‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
        ‖projectionFullL2 (projectedSourceQ A z)‖ +
          C * (A.slope : ℝ) * projectedSourceGradientMass z := by
  obtain ⟨H, hH, est⟩ := exists_projectionLipschitzCommutatorL2_bound
  let C := 4 * (H + ‖projectionFullL2‖)
  refine ⟨C, by unfold C; positivity, fun A z => ?_⟩
  have hs :
      ‖projectedSourceCommutatorSum A z‖ ≤
        4 * (H * (A.slope : ℝ)) * projectedSourceGradientMass z := by
    apply matrixDoubleSum_norm_le
    intro a b
    exact est a (A.entry a b) (A.smooth a b) A.slope (A.lipschitz a b) (projectionMatrixDerivative b z)
  have hc := projectedSourceCoefficientCorrection_norm_le A z
  rw [projectedSourceDivergenceL2_eq_projected]
  calc
    _ ≤ ‖-projectionFullL2 (projectedSourceQ A z) + projectedSourceCommutatorSum A z‖ +
        ‖projectedSourceCoefficientCorrection A (projectionFullSchwartz z)‖ := norm_sub_le _ _
    _ ≤ ‖projectionFullL2 (projectedSourceQ A z)‖ + ‖projectedSourceCommutatorSum A z‖ +
        ‖projectedSourceCoefficientCorrection A (projectionFullSchwartz z)‖ := by
      exact add_le_add_right ((norm_add_le _ _).trans_eq (by rw [norm_neg])) _
    _ ≤ ‖projectionFullL2 (projectedSourceQ A z)‖ + 4 * (H * (A.slope : ℝ)) * projectedSourceGradientMass z +
        4 * ((A.slope : ℝ) * ‖projectionFullL2‖) * projectedSourceGradientMass z :=
      add_le_add (add_le_add_left hs _) hc
    _ = _ := by unfold C; ring

end Burnett.P01
