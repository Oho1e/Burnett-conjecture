import Burnett.Analysis.FrozenTransport.Ward.WardAffineHessianDensity
import Burnett.Analysis.FrozenTransport.Ward.WardLorentzComplexKernel
import Burnett.Analysis.FrozenScreen.Phase

set_option autoImplicit false
set_option maxRecDepth 6900
set_option maxHeartbeats 11700000

noncomputable section

namespace Burnett.Analysis.TransportWardSymbol

open Matrix Burnett.RicciSymbol Burnett.V06
open scoped Matrix

private def wardRealDensityComponent (B : Mat) (w : ℝ) (p : Cov) (J : Mat) (a b : Index) : ℝ :=
  w * ((∑ c, B a c * raiseSecond B (ricciSymbol B p J) c b) -
    (B a b * metricTrace B (ricciSymbol B p J)) / 2)

private theorem wardEinsteinDensity_re (B : Mat) (w : ℝ) (p : Cov) (J : ComplexTensor2) (a b : Index) :
    (einsteinDensitySymbol B w p J a b).re = wardRealDensityComponent B w p (realAmplitude J) a b := by
  have h (z : ℂ) : (z / 2).re = z.re / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    simp only [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
    ring
  have hR : tensorRe (complexRicciSymbol B p J) = ricciSymbol B p (realAmplitude J) := by
    funext c d
    exact complexRicciSymbol_re B p J c d
  simp only [einsteinDensitySymbol, raiseBoth, wardRealDensityComponent, Complex.mul_re, Complex.sub_re,
    complex_re_fin_sum, Complex.ofReal_re, Complex.ofReal_im, h, complexRaiseSecond_re,
    complexMetricTrace_re, hR, zero_mul, sub_zero]

private theorem wardEinsteinDensity_im (B : Mat) (w : ℝ) (p : Cov) (J : ComplexTensor2) (a b : Index) :
    (einsteinDensitySymbol B w p J a b).im = wardRealDensityComponent B w p (imagAmplitude J) a b := by
  have h (z : ℂ) : (z / 2).im = z.im / 2 := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num]
    simp only [Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
    ring
  have hI : tensorIm (complexRicciSymbol B p J) = ricciSymbol B p (imagAmplitude J) := by
    funext c d
    exact complexRicciSymbol_im B p J c d
  simp only [einsteinDensitySymbol, raiseBoth, wardRealDensityComponent, Complex.mul_im, Complex.sub_im,
    complex_im_fin_sum, Complex.ofReal_re, Complex.ofReal_im, h, complexRaiseSecond_im,
    complexMetricTrace_im, hI, zero_mul, add_zero]

private theorem wardRealDensityPairing_eq_physical (B : Mat) (w : ℝ) (p : Cov) (J L : Mat) :
    ∑ a, ∑ b, L a b * wardRealDensityComponent B w p J a b =
      w * physicalPairing B L (ricciSymbol B p J) := by
  let R := ricciSymbol B p J
  have h (a b : Index) :
      L a b * wardRealDensityComponent B w p J a b =
        w * ((∑ c, ∑ d, B a c * B b d * L a b * R c d) -
          B a b * L a b * metricTrace B R / 2) := by
    change L a b * (w * ((∑ c, B a c * ∑ d, B b d * R c d) -
      B a b * metricTrace B R / 2)) = _
    have hA : L a b * (∑ c, B a c * ∑ d, B b d * R c d) =
        ∑ c, ∑ d, B a c * B b d * L a b * R c d := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      apply Finset.sum_congr rfl
      intro d _
      ring
    rw [← mul_assoc, mul_comm (L a b) w, mul_assoc, mul_sub, hA]
    ring
  simp only [h, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    physicalPairing, tensorPairing, metricTrace, R]

/-- Pair the actual canonical Einstein density with a complex covariant
test amplitude. The bilinear pairing is in the manuscript's signed slots. -/
def wardEinsteinDensityPairing (B : Mat) (w : ℝ) (p : Cov) (J L : ComplexTensor2) : ℂ :=
  ∑ a, ∑ b, L a b * einsteinDensitySymbol B w p J a b

/-- For a genuine frozen Lorentz metric the complex Hessian is exactly the
pairing with the original density-weighted Fourier Einstein symbol. -/
theorem wardComplexHessianPairing_eq_einsteinDensity (G : Mat) (hG : IsUnit G) (hGsym : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (p : Cov) (J L : ComplexTensor2)
    (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L) :
    wardComplexHessianPairing G p J L = wardEinsteinDensityPairing (inverseMatrix G) (metricDensity G) p J L := by
  have h (K N : Mat) (hK : IsSymmetricTensor K) (hN : IsSymmetricTensor N) :
      principalHessianPairing G p K N =
        ∑ a, ∑ b, N a b * wardRealDensityComponent (inverseMatrix G) (metricDensity G) p K a b :=
    (principalHessianPairing_lorentz_eq_physical G hG hGsym f p K N hK hN).trans
      (wardRealDensityPairing_eq_physical (inverseMatrix G) (metricDensity G) p K N).symm
  have hJr := realAmplitude_symmetric J hJ
  have hJi := imagAmplitude_symmetric J hJ
  have hLr := realAmplitude_symmetric L hL
  have hLi := imagAmplitude_symmetric L hL
  apply Complex.ext
  · simp only [wardEinsteinDensityPairing, wardComplexHessianPairing,
      complex_re_fin_sum, Complex.mul_re, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero,
      wardEinsteinDensity_re, wardEinsteinDensity_im, Finset.sum_sub_distrib, h _ _ hJr hLr, h _ _ hJi hLi]
    rfl
  · simp only [wardEinsteinDensityPairing, wardComplexHessianPairing,
      complex_im_fin_sum, Complex.mul_im, Complex.add_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, one_mul, zero_add,
      wardEinsteinDensity_re, wardEinsteinDensity_im, Finset.sum_add_distrib, h _ _ hJr hLi, h _ _ hJi hLr]
    exact add_comm _ _

theorem wardComplexLieTensor_symmetric (B : Mat) (p : Cov) (v : ComplexCovector) (r : Cov) (L : ComplexTensor2)
    (hL : IsSymmetricComplexTensor L) : IsSymmetricComplexTensor (wardComplexLieTensor B p v r L) := by
  intro a b
  simp only [wardComplexLieTensor, complexPureGauge, hL a b]
  ring

/-- The actual complex frozen Ward identity in the original Einstein-density
contraction, before using any physical constraints on the two non-gauge legs. -/
theorem complexPrincipalVertex_one_pureGauge_ward_einsteinDensity (G : Mat) (hG : IsUnit G)
    (hGsym : IsSymmetricTensor G) (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (p q r : Cov) (v : ComplexCovector) (J L : ComplexTensor2)
    (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    complexPrincipalVertex G p (complexPureGauge p v) q J r L =
      -wardEinsteinDensityPairing (inverseMatrix G) (metricDensity G) q J
        (wardComplexLieTensor (inverseMatrix G) p v r L) -
      wardEinsteinDensityPairing (inverseMatrix G) (metricDensity G) r L
        (wardComplexLieTensor (inverseMatrix G) p v q J) := by
  rw [complexPrincipalVertex_one_pureGauge_ward_lorentz G hG hGsym f p q r v J L hJ hL hcon,
    wardComplexHessianPairing_eq_einsteinDensity G hG hGsym f q J _ hJ (wardComplexLieTensor_symmetric _ _ _ _ _ hL),
    wardComplexHessianPairing_eq_einsteinDensity G hG hGsym f r L _ hL (wardComplexLieTensor_symmetric _ _ _ _ _ hJ)]

end Burnett.Analysis.TransportWardSymbol
