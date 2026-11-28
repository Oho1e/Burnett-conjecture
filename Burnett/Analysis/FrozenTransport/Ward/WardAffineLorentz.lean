import Burnett.Analysis.FrozenTransport.Ward.WardAffineLie
import Burnett.Algebra.TensorFrame

set_option autoImplicit false
set_option maxRecDepth 6800
set_option maxHeartbeats 9500000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol Burnett.Geometry.TensorCoordinateChange
open scoped Matrix

theorem eta_eq_standardInverse : eta = TensorFrame.standardInverse := by
  classical
  ext a b
  simp only [eta, Matrix.diagonal_apply, etaSign, TensorFrame.standardInverse, TensorFrame.signature]

private theorem wardFrame_inverseMatrix (G : Mat) (f : TensorFrame.LorentzFrame (inverseMatrix G)) :
    Matrix.of f.components * eta * (Matrix.of f.components)ᵀ = inverseMatrix G := by
  apply Eq.trans _ f.inverseMetric_eq
  ext i j
  rw [Matrix.mul_apply]
  simp only [eta, Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply, TensorFrame.inverseMetric, etaSign, TensorFrame.signature]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The actual inverse-metric Lorentz frame gives an invertible affine
matrix taking the covariant frozen background to `eta`. -/
theorem wardFrame_affineEta (G : Mat) (hG : IsUnit G) (f : TensorFrame.LorentzFrame (inverseMatrix G)) :
    IsUnit (Matrix.of f.components) ∧ pullbackMetric G (Matrix.of f.components) = eta := by
  let A : Mat := Matrix.of f.components
  let W := pullbackMetric G A
  have hI : A * eta * Aᵀ = G⁻¹ := wardFrame_inverseMatrix G f
  have hg := (Matrix.isUnit_iff_isUnit_det G).mp hG
  have he : G * (A * eta * Aᵀ) = 1 := by
    rw [hI, Matrix.mul_nonsing_inv G hg]
  have hA' : A.det ≠ 0 := by
    intro hz
    have hn := congrArg Matrix.det he
    simp only [Matrix.det_mul, Matrix.det_transpose, hz, mul_zero, zero_mul, Matrix.det_one, zero_ne_one] at hn
  have hA : IsUnit A := (Matrix.isUnit_iff_isUnit_det A).mpr (isUnit_iff_ne_zero.mpr hA')
  have hAt : IsUnit Aᵀ := by
    apply (Matrix.isUnit_iff_isUnit_det Aᵀ).mpr
    rw [Matrix.det_transpose]
    exact (Matrix.isUnit_iff_isUnit_det A).mp hA
  have hEq : A * W⁻¹ * Aᵀ = A * eta * Aᵀ := (inverse_pullback_cancel G A hA).trans hI.symm
  have hWI : W⁻¹ = eta := hA.mul_right_inj.mp (hAt.mul_left_inj.mp hEq)
  have hWdet : IsUnit W.det := by
    simp only [W, pullbackMetric, Matrix.det_mul, Matrix.det_transpose]
    exact (((Matrix.isUnit_iff_isUnit_det A).mp hA).mul hg).mul ((Matrix.isUnit_iff_isUnit_det A).mp hA)
  have hWeta : W * eta = 1 := by
    rw [← hWI, Matrix.mul_nonsing_inv W hWdet]
  refine ⟨hA, ?_⟩
  calc
    W = W * (eta * eta) := by rw [eta_mul_eta, mul_one]
    _ = eta := by rw [← mul_assoc, hWeta, one_mul]

/-- Real off-shell Ward identity for the actual frozen Lorentzian action
coefficient with the original inverse frame, for arbitrary signed triads. -/
theorem principalVertex_one_pureGauge_ward_lorentz (G : Mat) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (p q r v : Cov) (J L : Mat) (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    principalVertex G p (pureGauge p v) q J r L =
      -principalHessianPairing G q J (lieTensorSymbol (inverseMatrix G) p v r L) -
        principalHessianPairing G r L (lieTensorSymbol (inverseMatrix G) p v q J) := by
  obtain ⟨hA,hη⟩ := wardFrame_affineEta G hG f
  exact principalVertex_one_pureGauge_ward_of_affine_eta (Matrix.of f.components) G hA hG hGsym hη p q r v J L hJ hL hcon

end Burnett.Analysis.TransportWardSymbol
