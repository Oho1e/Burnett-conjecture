import Burnett.Analysis.FrozenTransport.Ward.WardAffineVertex
import Burnett.Analysis.TransportWard.OneGauge

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 11200000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol Burnett.Geometry.TensorCoordinateChange
open scoped Matrix

theorem wardAffinePureGauge (A : Mat) (p v : Cov) :
    pullbackMetric (pureGauge p v) A = pureGauge (wardAffineCovector A p) (wardAffineCovector A v) := by
  have h (q u : Cov) : (pureGauge q u : Mat) = vecMulVec q u + vecMulVec u q := by
    ext a b
    simp only [pureGauge, Matrix.add_apply, vecMulVec_apply]
  simp only [h, pullbackMetric, mul_add, add_mul, mul_vecMulVec, vecMulVec_mul, mulVec_transpose, wardAffineCovector]

private theorem wardAffineRaisedGenerator (A G : Mat) (hA : IsUnit A) (v : Cov) :
    A *ᵥ raiseCovector (inverseMatrix (pullbackMetric G A)) (wardAffineCovector A v) =
      raiseCovector (inverseMatrix G) v := by
  change A *ᵥ ((pullbackMetric G A)⁻¹ *ᵥ (v ᵥ* A)) = G⁻¹ *ᵥ v
  rw [← mulVec_transpose, mulVec_mulVec, mulVec_mulVec, inverse_pullback_cancel G A hA]

private theorem wardLieTensorSymbol_eq_transport (B : Mat) (p v r : Cov) (L : Mat) :
    lieTensorSymbol B p v r L = (raiseCovector B v ⬝ᵥ r) • L + Matrix.of (pureGauge p (raiseCovector B v ᵥ* L)) := by
  ext a b
  have h : (fun d => ∑ i, raiseCovector B v i * L i d) = raiseCovector B v ᵥ* L := rfl
  simp only [lieTensorSymbol, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, dotProduct, Matrix.of_apply, h]

/-- The exact Fourier Lie insertion transforms in the same covariant slots
as each original Jacobi tensor. The contracted generator is raised with
the inverse of the same frozen metric. -/
theorem wardAffineLieTensor (A G : Mat) (hA : IsUnit A) (p v r : Cov) (L : Mat) :
    pullbackMetric (lieTensorSymbol (inverseMatrix G) p v r L) A =
      lieTensorSymbol (inverseMatrix (pullbackMetric G A)) (wardAffineCovector A p) (wardAffineCovector A v)
        (wardAffineCovector A r) (pullbackMetric L A) := by
  let V := raiseCovector (inverseMatrix G) v
  let V' := raiseCovector (inverseMatrix (pullbackMetric G A)) (wardAffineCovector A v)
  have hV : A *ᵥ V' = V := wardAffineRaisedGenerator A G hA v
  have hPair : V' ⬝ᵥ wardAffineCovector A r = V ⬝ᵥ r := by
    change V' ⬝ᵥ (r ᵥ* A) = V ⬝ᵥ r
    rw [← mulVec_transpose, dotProduct_mulVec, vecMul_transpose, hV]
  have hC : V' ᵥ* pullbackMetric L A = wardAffineCovector A (V ᵥ* L) := by
    change V' ᵥ* (Aᵀ * L * A) = (V ᵥ* L) ᵥ* A
    rw [← vecMul_vecMul, ← vecMul_vecMul, vecMul_transpose, hV]
  rw [wardLieTensorSymbol_eq_transport, wardLieTensorSymbol_eq_transport]
  change pullbackMetric ((V ⬝ᵥ r) • L + Matrix.of (pureGauge p (V ᵥ* L))) A =
    (V' ⬝ᵥ wardAffineCovector A r) • pullbackMetric L A +
      Matrix.of (pureGauge (wardAffineCovector A p) (V' ᵥ* pullbackMetric L A))
  rw [hPair, hC, ← wardAffinePureGauge]
  simp only [pullbackMetric, mul_add, add_mul, mul_smul_comm, smul_mul_assoc]
  ext a b
  rfl

/-- The actual real frozen Ward identity transported from canonical
Minkowski coordinates, without any equation on the frozen background. -/
theorem principalVertex_one_pureGauge_ward_of_affine_eta (A G : Mat) (hA : IsUnit A)
    (hG : IsUnit G) (hGsym : IsSymmetricTensor G) (hEta : pullbackMetric G A = eta)
    (p q r v : Cov) (J L : Mat) (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    principalVertex G p (pureGauge p v) q J r L =
      -principalHessianPairing G q J (lieTensorSymbol (inverseMatrix G) p v r L) -
        principalHessianPairing G r L (lieTensorSymbol (inverseMatrix G) p v q J) := by
  have hS : p + q + r = 0 := funext hcon
  have hS' : wardAffineCovector A p + wardAffineCovector A q + wardAffineCovector A r = 0 := by
    have h := congrArg (wardAffineCovector A) hS
    simpa only [wardAffineCovector, add_vecMul, zero_vecMul] using h
  have hAcon (a : Fin 4) : wardAffineCovector A p a + wardAffineCovector A q a + wardAffineCovector A r a = 0 :=
    congrFun hS' a
  have hA' : A.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hG' : G.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hV (a b : Fin 4) : pureGauge p v a b = pureGauge p v b a := by
    simp only [pureGauge]
    ring
  have hTilt := principalVertex_eta_one_pureGauge_ward (wardAffineCovector A p) (wardAffineCovector A q)
    (wardAffineCovector A r) (wardAffineCovector A v) (pullbackMetric J A) (pullbackMetric L A)
    (wardAffineMetric_symm A J hJ) (wardAffineMetric_symm A L hL) hAcon
  have hLieL := wardAffineLieTensor A G hA p v r L
  have hLieJ := wardAffineLieTensor A G hA p v q J
  rw [hEta, inverseMatrix_eta] at hLieL hLieJ
  rw [← wardAffinePureGauge, ← hLieL, ← hLieJ, ← hEta,
    principalVertex_affine A G hA hG' hGsym _ _ _ _ _ _ hV hJ hL,
    principalHessianPairing_affine A G hA hG hGsym q J _ hJ (lieTensorSymbol_symmetric _ _ _ _ L hL),
    principalHessianPairing_affine A G hA hG hGsym r L _ hL (lieTensorSymbol_symmetric _ _ _ _ J hJ)] at hTilt
  apply mul_left_cancel₀ (abs_ne_zero.mpr hA')
  exact hTilt.trans (by ring)

end Burnett.Analysis.TransportWardSymbol
