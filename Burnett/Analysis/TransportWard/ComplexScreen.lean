import Burnett.Analysis.TransportWard.ComplexWard

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 20000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

theorem principalHessianPairing_comm (G : Mat) (p : Cov) (J L : Mat) :
    principalHessianPairing G p J L = principalHessianPairing G p L J := by
  have hn (M : Mat) : planeJet (-p) M = (-1 : ℝ) • planeJet p M := by
    simpa only [neg_one_smul] using planeJet_smul_covector p M (-1 : ℝ)
  simp only [principalHessianPairing, metricKineticCoefficient, hn]
  simp only [kineticCoefficient_smul_right]
  simp only [kineticCoefficient_eq_cross]
  ring

theorem einsteinPairingEta_comm (p : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    einsteinPairingEta p J L = einsteinPairingEta p L J := by
  rw [←principalHessianPairing_eta_eq_einstein p J L hJ hL,
    ←principalHessianPairing_eta_eq_einstein p L J hL hJ]
  exact principalHessianPairing_comm eta p J L

theorem complexEinsteinPairingEta_comm (p : Cov) (J L : ComplexTensor2)
    (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L) :
    complexEinsteinPairingEta p J L = complexEinsteinPairingEta p L J := by
  apply Complex.ext
  · simp only [complexEinsteinPairingEta_re]
    rw [einsteinPairingEta_comm p (realAmplitude J) (realAmplitude L)
        (realAmplitude_symmetric J hJ) (realAmplitude_symmetric L hL),
      einsteinPairingEta_comm p (imagAmplitude J) (imagAmplitude L)
        (imagAmplitude_symmetric J hJ) (imagAmplitude_symmetric L hL)]
  · simp only [complexEinsteinPairingEta_im]
    rw [einsteinPairingEta_comm p (realAmplitude J) (imagAmplitude L)
        (realAmplitude_symmetric J hJ) (imagAmplitude_symmetric L hL),
      einsteinPairingEta_comm p (imagAmplitude J) (realAmplitude L)
        (imagAmplitude_symmetric J hJ) (realAmplitude_symmetric L hL)]
    ring

theorem complexPrincipalVertex_eta_one_pureGauge_ward_paper_order (p q r : Cov)
    (v : ComplexCovector) (J L : ComplexTensor2)
    (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    complexPrincipalVertex eta p (complexPureGauge p v) q J r L =
      -complexEinsteinPairingEta q (complexLieTensorSymbolEta p v r L) J -
        complexEinsteinPairingEta r (complexLieTensorSymbolEta p v q J) L := by
  rw [complexPrincipalVertex_eta_one_pureGauge_ward p q r v J L hJ hL hcon,
    complexEinsteinPairingEta_comm q J _ hJ (complexLieTensorSymbolEta_symmetric p v r L hL),
    complexEinsteinPairingEta_comm r L _ hL (complexLieTensorSymbolEta_symmetric p v q J hJ)]
/-- The original C_eta, extended complex bilinearly, with no conjugation. -/
def complexScreenCoefficientEta (J L : ComplexTensor2) : ℂ :=
  ((∑ a, ∑ b, ((etaSign a * etaSign b : ℝ) : ℂ) * J a b * L a b) -
    (1 / 2 : ℂ) * complexMetricTrace eta J * complexMetricTrace eta L) / 4

theorem complexScreenCoefficientEta_comm (J L : ComplexTensor2) :
    complexScreenCoefficientEta J L = complexScreenCoefficientEta L J := by
  unfold complexScreenCoefficientEta
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · ring

theorem complexScreenCoefficientEta_add_right (J L M : ComplexTensor2) :
    complexScreenCoefficientEta J (L + M) =
      complexScreenCoefficientEta J L + complexScreenCoefficientEta J M := by
  unfold complexScreenCoefficientEta complexMetricTrace
  simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem complexScreenCoefficientEta_smul_right (J L : ComplexTensor2) (z : ℂ) :
    complexScreenCoefficientEta J (z • L) = z * complexScreenCoefficientEta J L := by
  unfold complexScreenCoefficientEta complexMetricTrace
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (_ : ℂ) z, ←Finset.mul_sum]
  ring

theorem complexEinsteinSymbolEta_phase (p : Cov) (J : ComplexTensor2)
    (ht : complexMetricTrace eta J = 0) (hq : ∀ b, complexContracted eta p J b = 0)
    (a b : Fin 4) :
    complexEinsteinSymbolEta p J a b =
      ((symbolNorm eta p : ℂ) / 2) * ((etaSign a * etaSign b : ℝ) : ℂ) * J a b := by
  have hr (i j : Fin 4) : complexRicciSymbol eta p J i j =
      ((symbolNorm eta p : ℂ) / 2) * J i j := by
    simp only [complexRicciSymbol, ht, hq, mul_zero, add_zero, sub_zero]
    ring
  have htrace : complexMetricTrace eta (complexRicciSymbol eta p J) = 0 := by
    calc
      _ = ((symbolNorm eta p : ℂ) / 2) * complexMetricTrace eta J := by
        unfold complexMetricTrace
        simp_rw [hr, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [ht, mul_zero]
  rw [complexEinsteinSymbolEta, hr, htrace]
  ring

theorem complexEinsteinPairingEta_phase (p : Cov) (J L : ComplexTensor2)
    (ht : complexMetricTrace eta J = 0) (hq : ∀ b, complexContracted eta p J b = 0) :
    complexEinsteinPairingEta p J L =
      2 * (symbolNorm eta p : ℂ) * complexScreenCoefficientEta J L := by
  calc
    _ = ((symbolNorm eta p : ℂ) / 2) *
        (∑ a, ∑ b, ((etaSign a * etaSign b : ℝ) : ℂ) * J a b * L a b) := by
      unfold complexEinsteinPairingEta
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [complexEinsteinSymbolEta_phase p J ht hq]
      ring
    _ = _ := by
      unfold complexScreenCoefficientEta
      rw [ht]
      ring

theorem complexScreenCoefficientEta_lieTensorSymbol (p : Cov) (v : ComplexCovector)
    (r : Cov) (J L : ComplexTensor2) :
    complexScreenCoefficientEta J (complexLieTensorSymbolEta p v r L) =
      complexGeneratorPairEta v r * complexScreenCoefficientEta J L +
        complexScreenCoefficientEta J (complexPureGauge p (complexGaugeContractionEta v L)) := by
  have ht : complexLieTensorSymbolEta p v r L =
      complexGeneratorPairEta v r • L + complexPureGauge p (complexGaugeContractionEta v L) := by
    funext a b
    rfl
  rw [ht, complexScreenCoefficientEta_add_right, complexScreenCoefficientEta_smul_right]

theorem complexGeneratorPairEta_sub_right (v : ComplexCovector) (q r : Cov) :
    complexGeneratorPairEta v (q - r) = complexGeneratorPairEta v q - complexGeneratorPairEta v r := by
  simp only [complexGeneratorPairEta, Pi.sub_apply, Complex.ofReal_sub,
    mul_sub, Finset.sum_sub_distrib]

theorem complexGeneratorPairEta_conserved (p q r : Cov) (v : ComplexCovector)
    (hcon : ∀ a, p a + q a + r a = 0) :
    complexGeneratorPairEta v p + complexGeneratorPairEta v q + complexGeneratorPairEta v r = 0 := by
  unfold complexGeneratorPairEta
  rw [←Finset.sum_add_distrib, ←Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro i hi
  have hc : (p i : ℂ) + (q i : ℂ) + (r i : ℂ) = 0 := by
    exact_mod_cast hcon i
  calc
    _ = (etaSign i : ℂ) * v i * ((p i : ℂ) + (q i : ℂ) + (r i : ℂ)) := by ring
    _ = 0 := by rw [hc, mul_zero]

theorem complexPrincipalVertex_eta_lowGauge_screen (p q r : Cov) (v : ComplexCovector)
    (J L : ComplexTensor2) (hJ : IsSymmetricComplexTensor J) (hL : IsSymmetricComplexTensor L)
    (hcon : ∀ a, p a + q a + r a = 0)
    (htJ : complexMetricTrace eta J = 0) (hqJ : ∀ b, complexContracted eta q J b = 0)
    (htL : complexMetricTrace eta L = 0) (hrL : ∀ b, complexContracted eta r L b = 0) :
    complexPrincipalVertex eta p (complexPureGauge p v) q J r L =
      -((symbolNorm eta r - symbolNorm eta q : ℝ) : ℂ) * complexGeneratorPairEta v (q - r) *
        complexScreenCoefficientEta J L +
      complexGeneratorPairEta v p * ((symbolNorm eta q + symbolNorm eta r : ℝ) : ℂ) *
        complexScreenCoefficientEta J L -
      2 * (symbolNorm eta q : ℂ) *
        complexScreenCoefficientEta J (complexPureGauge p (complexGaugeContractionEta v L)) -
      2 * (symbolNorm eta r : ℂ) *
        complexScreenCoefficientEta L (complexPureGauge p (complexGaugeContractionEta v J)) := by
  rw [complexPrincipalVertex_eta_one_pureGauge_ward p q r v J L hJ hL hcon,
    complexEinsteinPairingEta_phase q J _ htJ hqJ,
    complexEinsteinPairingEta_phase r L _ htL hrL,
    complexScreenCoefficientEta_lieTensorSymbol, complexScreenCoefficientEta_lieTensorSymbol,
    complexScreenCoefficientEta_comm L J]
  have hc := complexGeneratorPairEta_conserved p q r v hcon
  have hp : complexGeneratorPairEta v p =
      -complexGeneratorPairEta v q - complexGeneratorPairEta v r := by
    calc
      _ = complexGeneratorPairEta v p -
          (complexGeneratorPairEta v p + complexGeneratorPairEta v q + complexGeneratorPairEta v r) := by
        rw [hc, sub_zero]
      _ = _ := by ring
  rw [hp, complexGeneratorPairEta_sub_right]
  push_cast
  ring

theorem complexPrincipalVertex_eta_three_pureGauge (p q r : Cov)
    (v w z : ComplexCovector) (hcon : ∀ a, p a + q a + r a = 0) :
    complexPrincipalVertex eta p (complexPureGauge p v)
      q (complexPureGauge q w) r (complexPureGauge r z) = 0 := by
  have hz (x y t : Cov) := principalVertex_eta_three_pureGauge p q r x y t hcon
  simp only [complexPrincipalVertex, realAmplitude_complexPureGauge, imagAmplitude_complexPureGauge,
    hz, sub_zero, add_zero, Complex.ofReal_zero, mul_zero]
end Burnett.Analysis.TransportWardSymbol
