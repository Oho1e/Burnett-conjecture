import Burnett.Analysis.TransportWard.Amplitude
import Burnett.Analysis.TransportWard.OneGauge
import Burnett.Algebra.ComplexPolarization

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 20000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

/-- The existing real part with an explicit matrix head for matrix operations. -/
def realAmplitude (H : ComplexTensor2) : Mat := tensorRe H

def imagAmplitude (H : ComplexTensor2) : Mat := tensorIm H

theorem realAmplitude_add (H K : ComplexTensor2) :
    realAmplitude (H + K) = realAmplitude H + realAmplitude K := by
  funext a b
  simp only [realAmplitude, tensorRe, Pi.add_apply, Matrix.add_apply, Complex.add_re]

theorem imagAmplitude_add (H K : ComplexTensor2) :
    imagAmplitude (H + K) = imagAmplitude H + imagAmplitude K := by
  funext a b
  simp only [imagAmplitude, tensorIm, Pi.add_apply, Matrix.add_apply, Complex.add_im]

theorem realAmplitude_smul (z : ℂ) (H : ComplexTensor2) :
    realAmplitude (z • H) = z.re • realAmplitude H + (-z.im) • imagAmplitude H := by
  funext a b
  simp only [realAmplitude, imagAmplitude, tensorRe, tensorIm, Pi.smul_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.mul_re]
  ring

theorem imagAmplitude_smul (z : ℂ) (H : ComplexTensor2) :
    imagAmplitude (z • H) = z.im • realAmplitude H + z.re • imagAmplitude H := by
  funext a b
  simp only [realAmplitude, imagAmplitude, tensorRe, tensorIm, Pi.smul_apply,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Complex.mul_im]
  ring

theorem realAmplitude_ofReal (H : Mat) : realAmplitude (tensorOfReal H) = H := by
  funext a b
  simp only [realAmplitude, tensorRe, tensorOfReal, Complex.ofReal_re]

theorem imagAmplitude_ofReal (H : Mat) : imagAmplitude (tensorOfReal H) = 0 := by
  funext a b
  simp only [imagAmplitude, tensorIm, tensorOfReal, Complex.ofReal_im, Matrix.zero_apply]

theorem realAmplitude_symmetric (H : ComplexTensor2) (hH : IsSymmetricComplexTensor H) :
    IsSymmetricTensor (realAmplitude H) := by
  intro a b
  exact congrArg Complex.re (hH a b)

theorem imagAmplitude_symmetric (H : ComplexTensor2) (hH : IsSymmetricComplexTensor H) :
    IsSymmetricTensor (imagAmplitude H) := by
  intro a b
  exact congrArg Complex.im (hH a b)

theorem principalVertex_zero_first_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (J L : Mat) : principalVertex G p 0 q J r L = 0 := by
  simpa only [zero_smul, zero_mul] using
    principalVertex_smul_first_amplitude G hG p (0 : Mat) q J r L (0 : ℝ)

theorem principalVertex_zero_second_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (H L : Mat) : principalVertex G p H q 0 r L = 0 := by
  simpa only [zero_smul, zero_mul] using
    principalVertex_smul_second_amplitude G hG p H q (0 : Mat) r L (0 : ℝ)

theorem principalVertex_zero_third_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (H J : Mat) : principalVertex G p H q J r 0 = 0 := by
  simpa only [zero_smul, zero_mul] using
    principalVertex_smul_third_amplitude G hG p H q J r (0 : Mat) (0 : ℝ)

/-- The canonical complex multilinear extension of the actual real vertex.
This is the eight real/imaginary terms; no Ward expression occurs in its definition. -/
def complexPrincipalVertex (G : Mat) (p : Cov) (H : ComplexTensor2) (q : Cov)
    (J : ComplexTensor2) (r : Cov) (L : ComplexTensor2) : ℂ :=
  ((principalVertex G p (realAmplitude H) q (realAmplitude J) r (realAmplitude L) -
    principalVertex G p (realAmplitude H) q (imagAmplitude J) r (imagAmplitude L) -
    principalVertex G p (imagAmplitude H) q (realAmplitude J) r (imagAmplitude L) -
    principalVertex G p (imagAmplitude H) q (imagAmplitude J) r (realAmplitude L) : ℝ) : ℂ) +
  Complex.I * ((principalVertex G p (imagAmplitude H) q (realAmplitude J) r (realAmplitude L) +
    principalVertex G p (realAmplitude H) q (imagAmplitude J) r (realAmplitude L) +
    principalVertex G p (realAmplitude H) q (realAmplitude J) r (imagAmplitude L) -
    principalVertex G p (imagAmplitude H) q (imagAmplitude J) r (imagAmplitude L) : ℝ) : ℂ)

theorem complexPrincipalVertex_add_first_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H K : ComplexTensor2) (q : Cov) (J : ComplexTensor2)
    (r : Cov) (L : ComplexTensor2) :
    complexPrincipalVertex G p (H + K) q J r L =
      complexPrincipalVertex G p H q J r L + complexPrincipalVertex G p K q J r L := by
  unfold complexPrincipalVertex
  simp only [realAmplitude_add, imagAmplitude_add,
    principalVertex_add_first_amplitude G hG]
  push_cast
  ring

theorem complexPrincipalVertex_smul_first_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : ComplexTensor2) (q : Cov) (J : ComplexTensor2)
    (r : Cov) (L : ComplexTensor2) (z : ℂ) :
    complexPrincipalVertex G p (z • H) q J r L = z * complexPrincipalVertex G p H q J r L := by
  unfold complexPrincipalVertex
  simp only [realAmplitude_smul, imagAmplitude_smul,
    principalVertex_add_first_amplitude G hG, principalVertex_smul_first_amplitude G hG]
  apply Complex.ext
  all_goals simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.add_im, Complex.mul_im]
  all_goals ring

theorem complexPrincipalVertex_swap_first_two (G : Mat) (p : Cov) (H : ComplexTensor2)
    (q : Cov) (J : ComplexTensor2) (r : Cov) (L : ComplexTensor2) :
    complexPrincipalVertex G p H q J r L = complexPrincipalVertex G q J p H r L := by
  unfold complexPrincipalVertex
  simp only [principalVertex_swap_first_two G p _ q _ r _]
  push_cast
  ring

theorem complexPrincipalVertex_cyclic (G : Mat) (p : Cov) (H : ComplexTensor2)
    (q : Cov) (J : ComplexTensor2) (r : Cov) (L : ComplexTensor2) :
    complexPrincipalVertex G p H q J r L = complexPrincipalVertex G q J r L p H := by
  unfold complexPrincipalVertex
  simp only [principalVertex_cyclic G p _ q _ r _]
  push_cast
  ring

theorem complexPrincipalVertex_add_second_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : ComplexTensor2) (q : Cov) (J K : ComplexTensor2) (r : Cov) (L : ComplexTensor2) :
    complexPrincipalVertex G p H q (J + K) r L =
      complexPrincipalVertex G p H q J r L + complexPrincipalVertex G p H q K r L := by
  rw [complexPrincipalVertex_swap_first_two G p H q (J + K) r L,
    complexPrincipalVertex_add_first_amplitude G hG,
    complexPrincipalVertex_swap_first_two G q J p H r L,
    complexPrincipalVertex_swap_first_two G q K p H r L]

theorem complexPrincipalVertex_smul_second_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : ComplexTensor2) (q : Cov) (J : ComplexTensor2)
    (r : Cov) (L : ComplexTensor2) (z : ℂ) :
    complexPrincipalVertex G p H q (z • J) r L = z * complexPrincipalVertex G p H q J r L := by
  rw [complexPrincipalVertex_swap_first_two G p H q (z • J) r L,
    complexPrincipalVertex_smul_first_amplitude G hG,
    complexPrincipalVertex_swap_first_two G q J p H r L]

theorem complexPrincipalVertex_add_third_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : ComplexTensor2) (q : Cov) (J : ComplexTensor2) (r : Cov) (L K : ComplexTensor2) :
    complexPrincipalVertex G p H q J r (L + K) =
      complexPrincipalVertex G p H q J r L + complexPrincipalVertex G p H q J r K := by
  rw [complexPrincipalVertex_cyclic G p H q J r (L + K),
    complexPrincipalVertex_add_second_amplitude G hG,
    ←complexPrincipalVertex_cyclic G p H q J r L,
    ←complexPrincipalVertex_cyclic G p H q J r K]

theorem complexPrincipalVertex_smul_third_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : ComplexTensor2) (q : Cov) (J : ComplexTensor2)
    (r : Cov) (L : ComplexTensor2) (z : ℂ) :
    complexPrincipalVertex G p H q J r (z • L) = z * complexPrincipalVertex G p H q J r L := by
  rw [complexPrincipalVertex_cyclic G p H q J r (z • L),
    complexPrincipalVertex_smul_second_amplitude G hG,
    ←complexPrincipalVertex_cyclic G p H q J r L]

theorem complexPrincipalVertex_ofReal (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (H J L : Mat) :
    complexPrincipalVertex G p (tensorOfReal H) q (tensorOfReal J) r (tensorOfReal L) =
      (principalVertex G p H q J r L : ℂ) := by
  simp only [complexPrincipalVertex, realAmplitude_ofReal, imagAmplitude_ofReal,
    principalVertex_zero_first_amplitude G hG, principalVertex_zero_second_amplitude G hG,
    principalVertex_zero_third_amplitude G hG]
  push_cast
  ring

theorem complexPrincipalVertex_frequency_homogeneity (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (H J L : ComplexTensor2) (s : ℝ) :
    complexPrincipalVertex G (s • p) H (s • q) J (s • r) L =
      (s : ℂ) ^ 2 * complexPrincipalVertex G p H q J r L := by
  simp only [complexPrincipalVertex, principalVertex_frequency_homogeneity G hG]
  push_cast
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

def realGaugePotential (v : ComplexCovector) : Cov := fun a => (v a).re

def imagGaugePotential (v : ComplexCovector) : Cov := fun a => (v a).im

theorem realAmplitude_complexPureGauge (p : Cov) (v : ComplexCovector) :
    realAmplitude (complexPureGauge p v) = pureGauge p (realGaugePotential v) := by
  funext a b
  simp only [realAmplitude, tensorRe, complexPureGauge, pureGauge, realGaugePotential,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem imagAmplitude_complexPureGauge (p : Cov) (v : ComplexCovector) :
    imagAmplitude (complexPureGauge p v) = pureGauge p (imagGaugePotential v) := by
  funext a b
  simp only [imagAmplitude, tensorIm, complexPureGauge, pureGauge, imagGaugePotential,
    Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring

theorem complex_re_fin_sum (f : Fin 4 → ℂ) : (∑ a, f a).re = ∑ a, (f a).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

theorem complex_im_fin_sum (f : Fin 4 → ℂ) : (∑ a, f a).im = ∑ a, (f a).im :=
  map_sum Complex.imAddGroupHom f Finset.univ

/-- The original Ricci trace-reversal/raising, complex bilinearly extended at real eta. -/
def complexEinsteinSymbolEta (p : Cov) (J : ComplexTensor2) : ComplexTensor2 := fun a b =>
  ((etaSign a * etaSign b : ℝ) : ℂ) * complexRicciSymbol eta p J a b -
    (((1 / 2) * eta a b : ℝ) : ℂ) * complexMetricTrace eta (complexRicciSymbol eta p J)

def complexEinsteinPairingEta (p : Cov) (J L : ComplexTensor2) : ℂ :=
  ∑ a, ∑ b, L a b * complexEinsteinSymbolEta p J a b

theorem complexEinsteinSymbolEta_re (p : Cov) (J : ComplexTensor2) (a b : Fin 4) :
    (complexEinsteinSymbolEta p J a b).re = einsteinSymbolEta p (realAmplitude J) a b := by
  have ht : tensorRe (complexRicciSymbol eta p J) = ricciSymbol eta p (realAmplitude J) := by
    funext i j
    exact complexRicciSymbol_re eta p J i j
  simp only [complexEinsteinSymbolEta, Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, complexRicciSymbol_re, complexMetricTrace_re, ht,
    zero_mul, sub_zero, einsteinSymbolEta]
  rfl

theorem complexEinsteinSymbolEta_im (p : Cov) (J : ComplexTensor2) (a b : Fin 4) :
    (complexEinsteinSymbolEta p J a b).im = einsteinSymbolEta p (imagAmplitude J) a b := by
  have ht : tensorIm (complexRicciSymbol eta p J) = ricciSymbol eta p (imagAmplitude J) := by
    funext i j
    exact complexRicciSymbol_im eta p J i j
  simp only [complexEinsteinSymbolEta, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im, complexRicciSymbol_im, complexMetricTrace_im, ht,
    zero_mul, add_zero, einsteinSymbolEta]
  rfl

theorem complexEinsteinPairingEta_re (p : Cov) (J L : ComplexTensor2) :
    (complexEinsteinPairingEta p J L).re =
      einsteinPairingEta p (realAmplitude J) (realAmplitude L) -
      einsteinPairingEta p (imagAmplitude J) (imagAmplitude L) := by
  simp only [complexEinsteinPairingEta, complex_re_fin_sum, Complex.mul_re,
    complexEinsteinSymbolEta_re, complexEinsteinSymbolEta_im, einsteinPairingEta,
    realAmplitude, imagAmplitude, tensorRe, tensorIm, Finset.sum_sub_distrib]

theorem complexEinsteinPairingEta_im (p : Cov) (J L : ComplexTensor2) :
    (complexEinsteinPairingEta p J L).im =
      einsteinPairingEta p (realAmplitude J) (imagAmplitude L) +
      einsteinPairingEta p (imagAmplitude J) (realAmplitude L) := by
  simp only [complexEinsteinPairingEta, complex_im_fin_sum, Complex.mul_im,
    complexEinsteinSymbolEta_re, complexEinsteinSymbolEta_im, einsteinPairingEta,
    realAmplitude, imagAmplitude, tensorRe, tensorIm, Finset.sum_add_distrib]
  ring

theorem einsteinPairingEta_add_right (p : Cov) (J L M : Mat) :
    einsteinPairingEta p J (L + M) = einsteinPairingEta p J L + einsteinPairingEta p J M := by
  simp only [einsteinPairingEta, Matrix.add_apply, add_mul, Finset.sum_add_distrib]

theorem einsteinPairingEta_sub_right (p : Cov) (J L M : Mat) :
    einsteinPairingEta p J (L - M) = einsteinPairingEta p J L - einsteinPairingEta p J M := by
  simp only [einsteinPairingEta, Matrix.sub_apply, sub_mul, Finset.sum_sub_distrib]

theorem raiseCovector_eta_entry (v : Cov) (a : Fin 4) :
    raiseCovector eta v a = etaSign a * v a := by
  simp [raiseCovector, eta, Matrix.diagonal_apply]

def complexGaugeContractionEta (v : ComplexCovector) (L : ComplexTensor2) : ComplexCovector :=
  fun d => ∑ i, (etaSign i : ℂ) * v i * L i d

def complexGeneratorPairEta (v : ComplexCovector) (r : Cov) : ℂ :=
  ∑ i, (etaSign i : ℂ) * v i * (r i : ℂ)

def complexLieTensorSymbolEta (p : Cov) (v : ComplexCovector) (r : Cov)
    (L : ComplexTensor2) : ComplexTensor2 := fun a b =>
  complexGeneratorPairEta v r * L a b + complexPureGauge p (complexGaugeContractionEta v L) a b

theorem realAmplitude_complexLieTensorSymbolEta (p : Cov) (v : ComplexCovector)
    (r : Cov) (L : ComplexTensor2) :
    realAmplitude (complexLieTensorSymbolEta p v r L) =
      lieTensorSymbol eta p (realGaugePotential v) r (realAmplitude L) -
      lieTensorSymbol eta p (imagGaugePotential v) r (imagAmplitude L) := by
  funext a b
  simp only [realAmplitude, imagAmplitude, tensorRe, tensorIm, complexLieTensorSymbolEta,
    complexGeneratorPairEta, complexGaugeContractionEta, complexPureGauge,
    realGaugePotential, imagGaugePotential, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.mul_im, complex_re_fin_sum, complex_im_fin_sum,
    lieTensorSymbol, pureGauge, raiseCovector_eta_entry, Matrix.sub_apply,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, Finset.sum_sub_distrib]
  ring

theorem imagAmplitude_complexLieTensorSymbolEta (p : Cov) (v : ComplexCovector)
    (r : Cov) (L : ComplexTensor2) :
    imagAmplitude (complexLieTensorSymbolEta p v r L) =
      lieTensorSymbol eta p (realGaugePotential v) r (imagAmplitude L) +
      lieTensorSymbol eta p (imagGaugePotential v) r (realAmplitude L) := by
  funext a b
  simp only [realAmplitude, imagAmplitude, tensorRe, tensorIm, complexLieTensorSymbolEta,
    complexGeneratorPairEta, complexGaugeContractionEta, complexPureGauge,
    realGaugePotential, imagGaugePotential, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.add_im, Complex.mul_im, complex_re_fin_sum, complex_im_fin_sum,
    lieTensorSymbol, pureGauge, raiseCovector_eta_entry, Matrix.add_apply,
    zero_mul, mul_zero, sub_zero, add_zero, zero_add, Finset.sum_add_distrib]
  ring

theorem complexLieTensorSymbolEta_symmetric (p : Cov) (v : ComplexCovector) (r : Cov)
    (L : ComplexTensor2) (hL : IsSymmetricComplexTensor L) :
    IsSymmetricComplexTensor (complexLieTensorSymbolEta p v r L) := by
  intro a b
  simp only [complexLieTensorSymbolEta, complexPureGauge, hL a b]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

theorem complexPrincipalVertex_eta_one_pureGauge_ward (p q r : Cov) (v : ComplexCovector)
    (J L : ComplexTensor2) (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    complexPrincipalVertex eta p (complexPureGauge p v) q J r L =
      -complexEinsteinPairingEta q J (complexLieTensorSymbolEta p v r L) -
        complexEinsteinPairingEta r L (complexLieTensorSymbolEta p v q J) := by
  have hJr := realAmplitude_symmetric J hJ
  have hJi := imagAmplitude_symmetric J hJ
  have hLr := realAmplitude_symmetric L hL
  have hLi := imagAmplitude_symmetric L hL
  have hw (w : Cov) (K M : Mat) (hK : IsSymmetricTensor K) (hM : IsSymmetricTensor M) :
      principalVertex eta p (pureGauge p w) q K r M =
        -einsteinPairingEta q K (lieTensorSymbol eta p w r M) -
          einsteinPairingEta r M (lieTensorSymbol eta p w q K) := by
    rw [principalVertex_eta_one_pureGauge_ward p q r w K M hK hM hcon,
      principalHessianPairing_eta_eq_einstein q K _ hK (lieTensorSymbol_symmetric eta p w r M hM),
      principalHessianPairing_eta_eq_einstein r M _ hM (lieTensorSymbol_symmetric eta p w q K hK)]
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
      Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_re, Complex.sub_re, complexEinsteinPairingEta_re,
      realAmplitude_complexLieTensorSymbolEta, imagAmplitude_complexLieTensorSymbolEta,
      einsteinPairingEta_sub_right, einsteinPairingEta_add_right, h000, h011, h101, h110]
    ring
  · simp only [complexPrincipalVertex, realAmplitude_complexPureGauge, imagAmplitude_complexPureGauge,
      Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, Complex.neg_im, Complex.sub_im, complexEinsteinPairingEta_im,
      realAmplitude_complexLieTensorSymbolEta, imagAmplitude_complexLieTensorSymbolEta,
      einsteinPairingEta_sub_right, einsteinPairingEta_add_right, h100, h010, h001, h111]
    ring

theorem complexEinsteinPairingEta_eq_zero_of_ricci_kernel (p : Cov) (J L : ComplexTensor2)
    (hR : ∀ a b, complexRicciSymbol eta p J a b = 0) :
    complexEinsteinPairingEta p J L = 0 := by
  simp only [complexEinsteinPairingEta, complexEinsteinSymbolEta, hR,
    complexMetricTrace, mul_zero, Finset.sum_const_zero, sub_zero]

theorem complexPrincipalVertex_eta_one_gauge_eq_zero_of_ricci_kernels (p q r : Cov)
    (v : ComplexCovector) (J L : ComplexTensor2)
    (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L)
    (hcon : ∀ a, p a + q a + r a = 0)
    (hRJ : ∀ a b, complexRicciSymbol eta q J a b = 0)
    (hRL : ∀ a b, complexRicciSymbol eta r L a b = 0) :
    complexPrincipalVertex eta p (complexPureGauge p v) q J r L = 0 := by
  rw [complexPrincipalVertex_eta_one_pureGauge_ward p q r v J L hJ hL hcon,
    complexEinsteinPairingEta_eq_zero_of_ricci_kernel q J _ hRJ,
    complexEinsteinPairingEta_eq_zero_of_ricci_kernel r L _ hRL]
  ring

end Burnett.Analysis.TransportWardSymbol
