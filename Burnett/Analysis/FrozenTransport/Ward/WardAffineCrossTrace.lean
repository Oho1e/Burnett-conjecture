import Burnett.Analysis.TransportWard.ThreeGauge
import Burnett.Geometry.ConnectionCoordinateChange

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 8000000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.Geometry.ConnectionCoordinateChange
open scoped Matrix

/-- The affine connection transformation is the ordinary connection change
with a constant coordinate Jacobian. -/
def wardAffineConnection (A : Mat) (C : Conn) : Conn := transformedConnection A C 0

theorem wardAffineConnection_matrix (A : Mat) (C : Conn) (b : Fin 4) :
    connectionMatrix (wardAffineConnection A C) b = A⁻¹ * directionalConnection A C b * A := by
  change transformedConnectionMatrix A (directionalConnection A C b) (connectionMatrix 0 b) = _
  have h0 : connectionMatrix 0 b = 0 := rfl
  rw [transformedConnectionMatrix, h0, add_zero, mul_assoc]

/-- The trace contraction used by the first mixed Gamma--Gamma term. -/
def wardConnectionTrace (C : Conn) : Cov := fun b => Matrix.trace (connectionMatrix C b)

theorem wardTrace_affineConjugation (A B : Mat) (hA : IsUnit A.det) :
    Matrix.trace (A⁻¹ * B * A) = Matrix.trace B := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, Matrix.mul_nonsing_inv A hA, one_mul]

theorem wardTrace_affineConjugation_mul (A B D : Mat) (hA : IsUnit A.det) :
    Matrix.trace ((A⁻¹ * B * A) * (A⁻¹ * D * A)) = Matrix.trace (B * D) := by
  calc
    _ = Matrix.trace (A⁻¹ * B * (A * A⁻¹) * D * A) := by congr 1; noncomm_ring
    _ = _ := by
      rw [Matrix.mul_nonsing_inv A hA, mul_one, mul_assoc (A⁻¹) B D]
      exact wardTrace_affineConjugation A (B * D) hA

theorem wardConnectionTrace_affine (A : Mat) (C : Conn) (hA : IsUnit A.det) :
    wardConnectionTrace (wardAffineConnection A C) = wardConnectionTrace C ᵥ* A := by
  funext b
  rw [wardConnectionTrace, wardAffineConnection_matrix, wardTrace_affineConjugation A _ hA,
    directionalConnection, Matrix.trace_sum]
  simp only [Matrix.trace_smul, smul_eq_mul, Matrix.vecMul, dotProduct, wardConnectionTrace, mul_comm]

/-- Literal rewriting of the action's actual mixed Gamma--Gamma contraction
as one trace row term minus a trace of two connection matrices. -/
theorem connectionCross_eq_trace_expression (C D : Conn)
    (hC : ∀ a b c, C a b c = C a c b) (b c : Fin 4) :
    connectionCross C D b c = (wardConnectionTrace C ᵥ* connectionMatrix D b) c -
      Matrix.trace (connectionMatrix C c * connectionMatrix D b) := by
  simp only [connectionCross, Finset.sum_sub_distrib, wardConnectionTrace,
    Matrix.vecMul, dotProduct, Matrix.trace, diag_apply, Matrix.mul_apply, connectionMatrix]
  congr 1
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  apply Finset.sum_congr rfl
  intro a _
  rw [hC a a e]

end Burnett.Analysis.TransportWardSymbol
