import Burnett.Analysis.FrozenTransport.Ward.WardAffineCrossTrace

set_option autoImplicit false
set_option maxRecDepth 6400
set_option maxHeartbeats 9000000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.Geometry.ConnectionCoordinateChange
open scoped Matrix

private theorem wardConnectionCross_affine_traceRow (A : Mat) (hA : IsUnit A.det) (C D : Conn) (b c : Fin 4) :
    (wardConnectionTrace (wardAffineConnection A C) ᵥ* connectionMatrix (wardAffineConnection A D) b) c =
      ∑ p : Fin 4, ∑ q : Fin 4, A p b * A q c * (wardConnectionTrace C ᵥ* connectionMatrix D p) q := by
  let v := wardConnectionTrace C
  let W := directionalConnection A D b
  let R (p : Fin 4) := v ᵥ* connectionMatrix D p
  have h (b : Fin 4) : (v ᵥ* A) ᵥ* (A⁻¹ * directionalConnection A D b * A) =
      ∑ p, A p b • (R p ᵥ* A) := by
    calc
      _ = ((((v ᵥ* A) ᵥ* A⁻¹) ᵥ* directionalConnection A D b) ᵥ* A) := by simp only [vecMul_vecMul, mul_assoc]
      _ = (v ᵥ* directionalConnection A D b) ᵥ* A := by
        rw [vecMul_vecMul v A A⁻¹, Matrix.mul_nonsing_inv A hA, vecMul_one]
      _ = _ := by
        simp only [directionalConnection, vecMul_sum, vecMul_smul, sum_vecMul, smul_vecMul, R]
  rw [wardConnectionTrace_affine A C hA, wardAffineConnection_matrix]
  change ((v ᵥ* A) ᵥ* (A⁻¹ * W * A)) c = _
  rw [congrFun (h b) c]
  change (∑ p, A p b • (R p ᵥ* A)) c = ∑ p, ∑ q, A p b * A q c * R p q
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.vecMul, dotProduct, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

private theorem wardConnectionCross_affine_tracePair (A : Mat) (hA : IsUnit A.det) (C D : Conn) (b c : Fin 4) :
    Matrix.trace (connectionMatrix (wardAffineConnection A C) c * connectionMatrix (wardAffineConnection A D) b) =
      ∑ p : Fin 4, ∑ q : Fin 4, A p b * A q c * Matrix.trace (connectionMatrix C q * connectionMatrix D p) := by
  rw [wardAffineConnection_matrix, wardAffineConnection_matrix, wardTrace_affineConjugation_mul A _ _ hA]
  simp only [directionalConnection, Finset.sum_mul, Finset.mul_sum, Matrix.trace_sum, smul_mul_assoc,
    mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

/-- The mixed Gamma--Gamma contraction transforms as an ordinary covariant
two-tensor under the affine change of the frozen coordinates. -/
theorem connectionCross_affine_covariance (A : Mat) (hA : IsUnit A) (C D : Conn)
    (hC : ∀ a b c, C a b c = C a c b) (b c : Fin 4) :
    connectionCross (wardAffineConnection A C) (wardAffineConnection A D) b c =
      ∑ p : Fin 4, ∑ q : Fin 4, A p b * A q c * connectionCross C D p q := by
  have hdet := (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hC' : ∀ a b c, wardAffineConnection A C a b c = wardAffineConnection A C a c b :=
    transformed_connection_torsion_free A C 0 hC (fun _ _ _ => rfl)
  rw [connectionCross_eq_trace_expression _ _ hC', wardConnectionCross_affine_traceRow A hdet,
    wardConnectionCross_affine_tracePair A hdet]
  simp only [connectionCross_eq_trace_expression C D hC, mul_sub, Finset.sum_sub_distrib]

end Burnett.Analysis.TransportWardSymbol
