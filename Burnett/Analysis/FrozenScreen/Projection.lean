import Burnett.Algebra.RicciSymbol
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.V06

open Matrix Burnett.RicciSymbol
open scoped Matrix

abbrev ScreenMatrix := Matrix Index Index ℝ

/-- The actual matrix A used by the paper to invert the metric on the
Euclidean screen and to keep the complement unchanged. -/
def screenMetricExtension (B Q : ScreenMatrix) : ScreenMatrix := Q * B * Q + (1 - Q)

/-- The actual inverse on the Euclidean screen. -/
def screenInverse (B Q : ScreenMatrix) : ScreenMatrix :=
  Q * (screenMetricExtension B Q)⁻¹ * Q

/-- The trace-adjusted Euclidean screen projection in the paper. -/
def frozenScreenProjection (B Q H : ScreenMatrix) : ScreenMatrix :=
  Q * H * Q - (Matrix.trace (B * (Q * H * Q)) / 2) • screenInverse B Q

private theorem screenInverse_mul_self (B Q : ScreenMatrix) (hQ : Q * Q = Q) :
    screenInverse B Q * Q = screenInverse B Q := by
  rw [screenInverse, mul_assoc, hQ]

private theorem screenInverse_left_mul_self (B Q : ScreenMatrix) (hQ : Q * Q = Q) :
    Q * screenInverse B Q = screenInverse B Q := by
  unfold screenInverse
  calc
    _ = (Q * Q) * (screenMetricExtension B Q)⁻¹ * Q := by noncomm_ring
    _ = _ := by rw [hQ]

/-- The inverse of A gives the inverse of B on the range of Q with exactly
the order of products in the paper. -/
theorem screenInverse_metric_mul (B Q : ScreenMatrix) (hQ : Q * Q = Q)
    (hA : IsUnit (screenMetricExtension B Q).det) :
    Q * B * screenInverse B Q = Q := by
  let A := screenMetricExtension B Q
  have hQA : Q * A = Q * B * Q := by
    unfold A screenMetricExtension
    calc
      _ = (Q * Q) * B * Q + Q - Q * Q := by noncomm_ring
      _ = _ := by rw [hQ]; abel
  change Q * B * (Q * A⁻¹ * Q) = Q
  calc
    _ = (Q * B * Q) * A⁻¹ * Q := by noncomm_ring
    _ = Q * (A * A⁻¹) * Q := by rw [← hQA, mul_assoc Q A A⁻¹]
    _ = Q := by rw [A.mul_nonsing_inv hA, mul_one, hQ]

theorem trace_screenInverse_metric (B Q : ScreenMatrix) (hQ : Q * Q = Q)
    (hA : IsUnit (screenMetricExtension B Q).det) :
    Matrix.trace (B * screenInverse B Q) = Matrix.trace Q := by
  let R := screenInverse B Q
  calc
    _ = Matrix.trace ((B * R) * Q) := by rw [mul_assoc, screenInverse_mul_self B Q hQ]
    _ = Matrix.trace (Q * (B * R)) := Matrix.trace_mul_comm _ _
    _ = _ := by rw [← mul_assoc, screenInverse_metric_mul B Q hQ hA]

/-- The actual trace-adjusted expression has zero B-trace and is supported
in the Euclidean screen, provided Q is a rank-two projection. -/
theorem frozenScreenProjection_range (B Q H : ScreenMatrix) (hQ : Q * Q = Q)
    (hT : Matrix.trace Q = 2) (hA : IsUnit (screenMetricExtension B Q).det) :
    let P := frozenScreenProjection B Q H
    Q * P = P ∧ P * Q = P ∧ Matrix.trace (B * P) = 0 := by
  intro P
  have hLeft : Q * (Q * H * Q) = Q * H * Q := by
    calc
      _ = (Q * Q) * H * Q := by noncomm_ring
      _ = _ := by rw [hQ]
  have hRight : Q * H * Q * Q = Q * H * Q := by rw [mul_assoc, hQ]
  refine ⟨?_, ?_, ?_⟩
  · change Q * frozenScreenProjection B Q H = _
    simp only [frozenScreenProjection, mul_sub, mul_smul_comm, hLeft,
      screenInverse_left_mul_self B Q hQ]
    rfl
  · change frozenScreenProjection B Q H * Q = _
    simp only [frozenScreenProjection, sub_mul, smul_mul_assoc, hRight,
      screenInverse_mul_self B Q hQ]
    rfl
  · change Matrix.trace (B * frozenScreenProjection B Q H) = _
    rw [frozenScreenProjection, mul_sub, mul_smul_comm, Matrix.trace_sub, Matrix.trace_smul,
      trace_screenInverse_metric B Q hQ hA, hT, smul_eq_mul]
    ring

/-- The explicit formula fixes the supported trace-free range and is
idempotent. -/
theorem frozenScreenProjection_idempotent (B Q H : ScreenMatrix) (hQ : Q * Q = Q)
    (hT : Matrix.trace Q = 2) (hA : IsUnit (screenMetricExtension B Q).det) :
    frozenScreenProjection B Q (frozenScreenProjection B Q H) = frozenScreenProjection B Q H := by
  obtain ⟨hLeft, hRight, hTrace⟩ := frozenScreenProjection_range B Q H hQ hT hA
  change Q * frozenScreenProjection B Q H * Q -
      (Matrix.trace (B * (Q * frozenScreenProjection B Q H * Q)) / 2) • screenInverse B Q = _
  rw [hLeft, hRight, hTrace, zero_div, zero_smul, sub_zero]

end Burnett.V06
