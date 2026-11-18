import Burnett.Analysis.TransportWard.OneGauge

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 20000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

/-- The real bilinear C_eta from paper 1763--1765, with ordered tensor indices. -/
def screenCoefficientEta (J L : Mat) : ℝ :=
  ((∑ a, ∑ b, etaSign a * etaSign b * J a b * L a b) -
    (1 / 2) * metricTrace eta J * metricTrace eta L) / 4

/-- Lower-index contraction L(V,.) for the raised real gauge generator V=eta^-1 v. -/
def gaugeContractionEta (v : Cov) (L : Mat) : Cov := fun d =>
  ∑ i, raiseCovector eta v i * L i d

theorem eta_raised_contract_eq_pair (v p : Cov) :
    (∑ i, raiseCovector eta v i * p i) = etaPair v p := by
  rw [etaPair_eq_sum]
  simp [raiseCovector, eta, Matrix.diagonal_apply]

theorem screenCoefficientEta_comm (J L : Mat) :
    screenCoefficientEta J L = screenCoefficientEta L J := by
  unfold screenCoefficientEta
  congr 1
  congr 1
  · apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    ring
  · ring

theorem screenCoefficientEta_add_right (J L M : Mat) :
    screenCoefficientEta J (L + M) = screenCoefficientEta J L + screenCoefficientEta J M := by
  unfold screenCoefficientEta metricTrace
  simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem screenCoefficientEta_smul_right (J L : Mat) (s : ℝ) :
    screenCoefficientEta J (s • L) = s * screenCoefficientEta J L := by
  unfold screenCoefficientEta metricTrace
  simp only [Matrix.smul_apply, smul_eq_mul]
  simp_rw [mul_left_comm (_ : ℝ) s, ←Finset.mul_sum]
  ring

theorem einsteinPairingEta_phase (p : Cov) (J L : Mat)
    (ht : metricTrace eta J = 0) (hq : ∀ b, contracted eta p J b = 0) :
    einsteinPairingEta p J L = 2 * symbolNorm eta p * screenCoefficientEta J L := by
  calc
    _ = (symbolNorm eta p / 2) * (∑ a, ∑ b,
        etaSign a * etaSign b * J a b * L a b) := by
      unfold einsteinPairingEta
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [einsteinSymbolEta_phase_of_tracefree_contracted p J ht hq]
      ring
    _ = _ := by
      unfold screenCoefficientEta
      rw [ht]
      ring

theorem screenCoefficientEta_lieTensorSymbol (p v r : Cov) (J L : Mat) :
    screenCoefficientEta J (lieTensorSymbol eta p v r L) =
      etaPair v r * screenCoefficientEta J L +
        screenCoefficientEta J (pureGauge p (gaugeContractionEta v L)) := by
  have ht : lieTensorSymbol eta p v r L =
      (etaPair v r) • L + gaugeMatrix p (gaugeContractionEta v L) := by
    funext a b
    change (∑ i, raiseCovector eta v i * r i) * L a b +
        pureGauge p (gaugeContractionEta v L) a b =
      etaPair v r * L a b + pureGauge p (gaugeContractionEta v L) a b
    rw [eta_raised_contract_eq_pair]
  rw [ht, screenCoefficientEta_add_right, screenCoefficientEta_smul_right]
  rfl

theorem etaPair_conserved (p q r v : Cov) (hcon : ∀ a, p a + q a + r a = 0) :
    etaPair v p + etaPair v q + etaPair v r = 0 := by
  have hr : r = -(p + q) := by
    funext a
    have h := hcon a
    simp only [Pi.neg_apply, Pi.add_apply]
    linarith
  rw [hr, etaPair_neg_right, etaPair_add_right]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

theorem principalVertex_eta_lowGauge_screen (p q r v : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L)
    (hcon : ∀ a, p a + q a + r a = 0)
    (htJ : metricTrace eta J = 0) (hqJ : ∀ b, contracted eta q J b = 0)
    (htL : metricTrace eta L = 0) (hrL : ∀ b, contracted eta r L b = 0) :
    principalVertex eta p (pureGauge p v) q J r L =
      -(symbolNorm eta r - symbolNorm eta q) * etaPair v (q - r) * screenCoefficientEta J L +
      etaPair v p * (symbolNorm eta q + symbolNorm eta r) * screenCoefficientEta J L -
      2 * symbolNorm eta q * screenCoefficientEta J (pureGauge p (gaugeContractionEta v L)) -
      2 * symbolNorm eta r * screenCoefficientEta L (pureGauge p (gaugeContractionEta v J)) := by
  have hWard := principalVertex_eta_one_pureGauge_ward p q r v J L hJ hL hcon
  rw [hWard,
    principalHessianPairing_eta_eq_einstein q J _ hJ (lieTensorSymbol_symmetric eta p v r L hL),
    principalHessianPairing_eta_eq_einstein r L _ hL (lieTensorSymbol_symmetric eta p v q J hJ),
    einsteinPairingEta_phase q J _ htJ hqJ,
    einsteinPairingEta_phase r L _ htL hrL,
    screenCoefficientEta_lieTensorSymbol, screenCoefficientEta_lieTensorSymbol,
    screenCoefficientEta_comm L J]
  have hcon' := etaPair_conserved p q r v hcon
  have hp : etaPair v p = -etaPair v q - etaPair v r := by linarith
  have hsub : etaPair v (q - r) = etaPair v q - etaPair v r := by
    rw [sub_eq_add_neg, etaPair_add_right, etaPair_neg_right]
    rfl
  rw [hp, hsub]
  ring

end Burnett.Analysis.TransportWardSymbol
