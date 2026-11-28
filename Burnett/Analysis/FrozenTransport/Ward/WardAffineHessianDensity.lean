import Burnett.Analysis.FrozenTransport.Ward.WardAffineLorentz

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 11200000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol Burnett.Geometry.TensorCoordinateChange
open scoped Matrix

private theorem wardFrame_tensor_mul (A : Mat) (c : ℝ) (H : Mat) :
    TensorFrame.tensor A (c • H) = c • TensorFrame.tensor A H := by
  ext a b
  change TensorFrame.tensor A (c • H) a b = c * TensorFrame.tensor A H a b
  simp only [TensorFrame.tensor, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem wardFrame_tensor_add (A H J : Mat) :
    TensorFrame.tensor A (H + J) = TensorFrame.tensor A H + TensorFrame.tensor A J :=
  TensorFrame.tensor_add A H J

private theorem wardFrame_tensor_sub (A H J : Mat) :
    TensorFrame.tensor A (H - J) = TensorFrame.tensor A H - TensorFrame.tensor A J := by
  rw [sub_eq_add_neg, TensorFrame.tensor_add, ← neg_one_smul ℝ J, wardFrame_tensor_mul, neg_one_smul, sub_eq_add_neg]

private theorem wardFrame_tensor_rank_one (A : Mat) (u v : Cov) :
    TensorFrame.tensor A (vecMulVec u v) = vecMulVec (TensorFrame.covector A u) (TensorFrame.covector A v) := by
  ext a b
  exact TensorFrame.tensor_product A u v a b

private theorem wardRicciSymbol_eq_rank_one (B : Mat) (p : Cov) (H : Mat) :
    (ricciSymbol B p H : Mat) = (symbolNorm B p / 2) • H +
      (metricTrace B H / 2) • vecMulVec p p - (1 / 2 : ℝ) • vecMulVec p (contracted B p H) -
      (1 / 2 : ℝ) • vecMulVec (contracted B p H) p := by
  ext a b
  simp only [ricciSymbol, Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, vecMulVec_apply]
  ring

/-- Exact covariance of the off-cone Ricci symbol, with both tensor indices
transported by the same ordered Lorentz frame. -/
theorem wardRicciSymbol_frame (A : Mat) (p : Cov) (H : Mat) :
    TensorFrame.tensor A (ricciSymbol (TensorFrame.inverseMetric A) p H) =
      ricciSymbol TensorFrame.standardInverse (TensorFrame.covector A p) (TensorFrame.tensor A H) := by
  have hTr : metricTrace (TensorFrame.inverseMetric A) H = metricTrace TensorFrame.standardInverse (TensorFrame.tensor A H) :=
    (TensorFrame.metricTrace_transform A H).trans (TensorFrame.metricTrace_standard _).symm
  have hC : TensorFrame.covector A (contracted (TensorFrame.inverseMetric A) p H) =
      contracted TensorFrame.standardInverse (TensorFrame.covector A p) (TensorFrame.tensor A H) := by
    funext a
    exact (TensorFrame.contracted_transform A H p a).symm
  rw [wardRicciSymbol_eq_rank_one, wardRicciSymbol_eq_rank_one]
  simp only [wardFrame_tensor_sub, wardFrame_tensor_add, wardFrame_tensor_mul, wardFrame_tensor_rank_one,
    TensorFrame.symbolNorm_transform, hTr, hC]

private theorem wardAffineCovector_eq_frame (A : Mat) (p : Cov) : wardAffineCovector A p = TensorFrame.covector A p := by
  funext a
  simp only [wardAffineCovector, TensorFrame.covector, Matrix.vecMul, dotProduct, mul_comm]

private theorem wardAffineTensor_eq_frame (A H : Mat) : pullbackMetric H A = TensorFrame.tensor A H := by
  ext a b
  simp only [pullbackMetric, TensorFrame.tensor, Matrix.mul_apply, transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem wardEinsteinPairingEta_eq_physical (p : Cov) (J L : Mat) :
    einsteinPairingEta p J L = physicalPairing eta L (ricciSymbol eta p J) := by
  have hDiag : ∑ a, ∑ b, L a b * ((1 / 2 : ℝ) * eta a b * metricTrace eta (ricciSymbol eta p J)) =
      metricTrace eta L * metricTrace eta (ricciSymbol eta p J) / 2 := by
    simp only [metricTrace, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  unfold einsteinPairingEta einsteinSymbolEta
  simp only [mul_sub, Finset.sum_sub_distrib, hDiag, physicalPairing]
  congr 1
  conv_rhs => rw [eta_eq_standardInverse, TensorFrame.tensorPairing_standard]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [eta_eq_standardInverse, etaSign, TensorFrame.signature]
  ring

/-- The real Hessian of the true frozen ΓΓ action pairs with the actual
density-weighted trace reversal at every nondegenerate Lorentz background. -/
theorem principalHessianPairing_lorentz_eq_physical (G : Mat) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (p : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    principalHessianPairing G p J L =
      metricDensity G * physicalPairing (inverseMatrix G) L (ricciSymbol (inverseMatrix G) p J) := by
  let A : Mat := Matrix.of f.components
  obtain ⟨hA,hη⟩ := wardFrame_affineEta G hG f
  have hA' : A.det ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hw := metricDensity_affine A G
  rw [hη, metricDensity_eta] at hw
  have hP := principalHessianPairing_affine A G hA hG hGsym p J L hJ hL
  rw [hη, principalHessianPairing_eta_eq_einstein _ _ _ (wardAffineMetric_symm A J hJ) (wardAffineMetric_symm A L hL),
    wardEinsteinPairingEta_eq_physical, wardAffineCovector_eq_frame, wardAffineTensor_eq_frame, wardAffineTensor_eq_frame,
    eta_eq_standardInverse, ← wardRicciSymbol_frame, ← TensorFrame.physicalPairing_transform] at hP
  have hB : TensorFrame.inverseMetric A = inverseMatrix G := f.inverseMetric_eq
  rw [hB] at hP
  apply mul_left_cancel₀ (abs_ne_zero.mpr hA')
  calc
    _ = physicalPairing (inverseMatrix G) L (ricciSymbol (inverseMatrix G) p J) := hP.symm
    _ = _ := by rw [← mul_assoc, ← hw, one_mul]

end Burnett.Analysis.TransportWardSymbol
