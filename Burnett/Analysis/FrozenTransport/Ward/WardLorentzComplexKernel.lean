import Burnett.Analysis.FrozenTransport.Ward.WardAffineLorentz
import Burnett.Analysis.TransportWard.ComplexWard

set_option autoImplicit false
set_option maxRecDepth 7200
set_option maxHeartbeats 11800000
noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol
open scoped Matrix

private def wardComplexRaisedGenerator (B : Mat) (v : ComplexCovector) (i : Fin 4) : ℂ :=
  ∑ j, (B i j : ℂ) * v j

/-- Bilinearly complexified insertion of the true raised gauge generator. -/
def wardComplexLieTensor (B : Mat) (p : Cov) (v : ComplexCovector) (r : Cov) (L : ComplexTensor2) : ComplexTensor2 :=
  fun a b => (∑ i, wardComplexRaisedGenerator B v i * (r i : ℂ)) * L a b +
    complexPureGauge p (fun d => ∑ i, wardComplexRaisedGenerator B v i * L i d) a b

private theorem wardComplexRaisedGenerator_re (B : Mat) (v : ComplexCovector) (i : Fin 4) :
    (wardComplexRaisedGenerator B v i).re = raiseCovector B (realGaugePotential v) i := by
  simp only [wardComplexRaisedGenerator, complex_re_fin_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    raiseCovector, realGaugePotential, zero_mul, sub_zero]

private theorem wardComplexRaisedGenerator_im (B : Mat) (v : ComplexCovector) (i : Fin 4) :
    (wardComplexRaisedGenerator B v i).im = raiseCovector B (imagGaugePotential v) i := by
  simp only [wardComplexRaisedGenerator, complex_im_fin_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    raiseCovector, imagGaugePotential, zero_mul, add_zero]

private theorem wardComplexLieTensor_re (B : Mat) (p : Cov) (v : ComplexCovector) (r : Cov) (L : ComplexTensor2) :
    realAmplitude (wardComplexLieTensor B p v r L) =
      lieTensorSymbol B p (realGaugePotential v) r (realAmplitude L) -
      lieTensorSymbol B p (imagGaugePotential v) r (imagAmplitude L) := by
  ext a b
  simp only [realAmplitude, imagAmplitude, tensorRe, tensorIm, wardComplexLieTensor, complexPureGauge,
    lieTensorSymbol, pureGauge, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    complex_re_fin_sum, complex_im_fin_sum, wardComplexRaisedGenerator_re, wardComplexRaisedGenerator_im,
    zero_mul, mul_zero, sub_zero, zero_add, Finset.sum_sub_distrib, Matrix.sub_apply]
  ring

private theorem wardComplexLieTensor_im (B : Mat) (p : Cov) (v : ComplexCovector) (r : Cov) (L : ComplexTensor2) :
    imagAmplitude (wardComplexLieTensor B p v r L) =
      lieTensorSymbol B p (realGaugePotential v) r (imagAmplitude L) +
      lieTensorSymbol B p (imagGaugePotential v) r (realAmplitude L) := by
  ext a b
  simp only [realAmplitude, imagAmplitude, tensorRe, tensorIm, wardComplexLieTensor, complexPureGauge,
    lieTensorSymbol, pureGauge, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    complex_re_fin_sum, complex_im_fin_sum, wardComplexRaisedGenerator_re, wardComplexRaisedGenerator_im,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, Finset.sum_add_distrib, Matrix.add_apply]
  ring

private theorem principalHessianPairing_add_right (G : Mat) (p : Cov) (J L M : Mat) :
    principalHessianPairing G p J (L + M) = principalHessianPairing G p J L + principalHessianPairing G p J M := by
  simp only [principalHessianPairing, metricKineticCoefficient, planeJet_add_amplitude, kineticCoefficient_eq_cross,
    gammaCross_add_left, gammaCross_add_right]
  ring

private theorem principalHessianPairing_sub_right (G : Mat) (p : Cov) (J L M : Mat) :
    principalHessianPairing G p J (L - M) = principalHessianPairing G p J L - principalHessianPairing G p J M := by
  have h : principalHessianPairing G p J (-M) = -principalHessianPairing G p J M := by
    rw [← neg_one_smul ℝ M]
    simp only [principalHessianPairing, metricKineticCoefficient, planeJet_smul_amplitude, kineticCoefficient_eq_cross,
      gammaCross_smul_left, gammaCross_smul_right]
    ring
  rw [sub_eq_add_neg, principalHessianPairing_add_right, h, sub_eq_add_neg]

/-- Complex bilinear extension of the canonical real frozen Hessian. -/
def wardComplexHessianPairing (G : Mat) (p : Cov) (J L : ComplexTensor2) : ℂ :=
  ((principalHessianPairing G p (realAmplitude J) (realAmplitude L) -
    principalHessianPairing G p (imagAmplitude J) (imagAmplitude L) : ℝ) : ℂ) +
  Complex.I * ((principalHessianPairing G p (realAmplitude J) (imagAmplitude L) +
    principalHessianPairing G p (imagAmplitude J) (realAmplitude L) : ℝ) : ℂ)

/-- The actual full frozen complex vertex satisfies the off-shell Ward
identity at the same general Lorentz frame, with all signed slots fixed. -/
theorem complexPrincipalVertex_one_pureGauge_ward_lorentz (G : Mat) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (p q r : Cov) (v : ComplexCovector) (J L : ComplexTensor2)
    (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    complexPrincipalVertex G p (complexPureGauge p v) q J r L =
      -wardComplexHessianPairing G q J (wardComplexLieTensor (inverseMatrix G) p v r L) -
        wardComplexHessianPairing G r L (wardComplexLieTensor (inverseMatrix G) p v q J) := by
  have hJr := realAmplitude_symmetric J hJ
  have hJi := imagAmplitude_symmetric J hJ
  have hLr := realAmplitude_symmetric L hL
  have hLi := imagAmplitude_symmetric L hL
  have hw (u : Cov) (K N : Mat) (hK : IsSymmetricTensor K) (hN : IsSymmetricTensor N) :
      principalVertex G p (pureGauge p u) q K r N =
        -principalHessianPairing G q K (lieTensorSymbol (inverseMatrix G) p u r N) -
          principalHessianPairing G r N (lieTensorSymbol (inverseMatrix G) p u q K) :=
    principalVertex_one_pureGauge_ward_lorentz G hG hGsym f p q r u K N hK hN hcon
  have h000 := hw (realGaugePotential v) (realAmplitude J) (realAmplitude L) hJr hLr
  have h011 := hw (realGaugePotential v) (imagAmplitude J) (imagAmplitude L) hJi hLi
  have h101 := hw (imagGaugePotential v) (realAmplitude J) (imagAmplitude L) hJr hLi
  have h110 := hw (imagGaugePotential v) (imagAmplitude J) (realAmplitude L) hJi hLr
  have h100 := hw (imagGaugePotential v) (realAmplitude J) (realAmplitude L) hJr hLr
  have h010 := hw (realGaugePotential v) (imagAmplitude J) (realAmplitude L) hJi hLr
  have h001 := hw (realGaugePotential v) (realAmplitude J) (imagAmplitude L) hJr hLi
  have h111 := hw (imagGaugePotential v) (imagAmplitude J) (imagAmplitude L) hJi hLi
  apply Complex.ext
  · simp only [complexPrincipalVertex, realAmplitude_complexPureGauge, imagAmplitude_complexPureGauge,
      wardComplexHessianPairing, wardComplexLieTensor_re, wardComplexLieTensor_im, principalHessianPairing_add_right,
      principalHessianPairing_sub_right, Complex.add_re, Complex.sub_re, Complex.neg_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
      h000, h011, h101, h110]
    ring
  · simp only [complexPrincipalVertex, realAmplitude_complexPureGauge, imagAmplitude_complexPureGauge,
      wardComplexHessianPairing, wardComplexLieTensor_re, wardComplexLieTensor_im, principalHessianPairing_add_right,
      principalHessianPairing_sub_right, Complex.add_im, Complex.sub_im, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, one_mul, zero_add,
      h100, h010, h001, h111]
    ring

end Burnett.Analysis.TransportWardSymbol
