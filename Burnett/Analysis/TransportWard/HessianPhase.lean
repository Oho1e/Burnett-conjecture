import Burnett.Analysis.TransportWard.ThreeGauge

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

def connectionCrossVariation (C DC D DD : Conn) (b c : Fin 4) : ℝ :=
  ∑ a, ∑ e, ((DC a a e * D e b c + C a a e * DD e b c) -
    (DC a c e * D e b a + C a c e * DD e b a))

theorem hasDerivAt_connectionCross (C D : ℝ → Conn) (DC DD : Conn)
    (hC : ∀ a b c, HasDerivAt (fun t => C t a b c) (DC a b c) 0)
    (hD : ∀ a b c, HasDerivAt (fun t => D t a b c) (DD a b c) 0) (b c : Fin 4) :
    HasDerivAt (fun t => connectionCross (C t) (D t) b c)
      (connectionCrossVariation (C 0) DC (D 0) DD b c) 0 := by
  unfold connectionCross connectionCrossVariation
  exact HasDerivAt.fun_sum (fun a _ => HasDerivAt.fun_sum (fun e _ =>
    ((hC a a e).mul (hD e b c)).sub ((hC a c e).mul (hD e b a))))

def gammaCrossVariation (G H : Mat) (X Y : Jet) : ℝ :=
  ∑ b, ∑ c, (inverseVariation G H b c *
    connectionCross (christoffel (inverseMatrix G) X) (christoffel (inverseMatrix G) Y) b c +
    inverseMatrix G b c * connectionCrossVariation
      (christoffel (inverseMatrix G) X) (connectionVariation G H X)
      (christoffel (inverseMatrix G) Y) (connectionVariation G H Y) b c)

theorem hasDerivAt_gammaCross_inverse_path (G H : Mat) (hG : Matrix.det G ≠ 0) (X Y : Jet) :
    HasDerivAt (fun t : ℝ => gammaCross (inverseMatrix (G + t • H)) X Y)
      (gammaCrossVariation G H X Y) 0 := by
  have hc := hasDerivAt_christoffel_inverse_path G H hG X
  have hd := hasDerivAt_christoffel_inverse_path G H hG Y
  have hQ (b c : Fin 4) := hasDerivAt_connectionCross
    (fun t => christoffel (inverseMatrix (G + t • H)) X)
    (fun t => christoffel (inverseMatrix (G + t • H)) Y)
    (connectionVariation G H X) (connectionVariation G H Y) hc hd b c
  unfold gammaCross gammaCrossVariation
  simpa only [zero_smul, add_zero] using
    HasDerivAt.fun_sum (fun b _ => HasDerivAt.fun_sum (fun c _ =>
      (hasDerivAt_inverseMatrix_entry_path G H hG b c).mul (hQ b c)))

theorem principalLeg_eq_cross_variation (G H : Mat) (hG : Matrix.det G ≠ 0) (X Y : Jet) :
    principalLeg G H X Y =
      (metricDensity G / 2 * traceVariation G H) *
        (gammaCross (inverseMatrix G) X Y + gammaCross (inverseMatrix G) Y X) +
      metricDensity G * (gammaCrossVariation G H X Y + gammaCrossVariation G H Y X) := by
  have ht := (hasDerivAt_metricDensity_path G H hG).mul
    ((hasDerivAt_gammaCross_inverse_path G H hG X Y).add
      (hasDerivAt_gammaCross_inverse_path G H hG Y X))
  have hnew : HasDerivAt (fun t : ℝ => metricKineticCoefficient (G + t • H) X Y)
      ((metricDensity G / 2 * traceVariation G H) *
        (gammaCross (inverseMatrix G) X Y + gammaCross (inverseMatrix G) Y X) +
      metricDensity G * (gammaCrossVariation G H X Y + gammaCrossVariation G H Y X)) 0 := by
    simpa only [metricKineticCoefficient, kineticCoefficient_eq_cross, Pi.add_apply,
      zero_smul, add_zero] using ht
  exact (hasDerivAt_metricKineticCoefficient_path G H hG X Y).unique hnew

theorem inverseMatrix_eta : inverseMatrix eta = eta := matrixInverse_eta

theorem principalLeg_eta_eq_cross_variation (H : Mat) (X Y : Jet) :
    principalLeg eta H X Y =
      (1 / 2 * traceVariation eta H) * (gammaCross eta X Y + gammaCross eta Y X) +
      gammaCrossVariation eta H X Y + gammaCrossVariation eta H Y X := by
  rw [principalLeg_eq_cross_variation eta H (det_ne_zero_of_right_inverse eta eta eta_mul_eta),
    metricDensity_eta, inverseMatrix_eta]
  ring

/-- Actual Fourier GammaGamma principal Hessian: the two coordinate derivatives
contribute i^2=-1, and the second signed frequency is opposite. -/
def principalHessianPairing (G : Mat) (p : Cov) (J L : Mat) : ℝ :=
  -metricKineticCoefficient G (planeJet p J) (planeJet (-p) L)

/-- Raised generator and full linearized Lie tensor at the other frequency.
This includes both the transport and tensor-index terms. -/
def lieTensorSymbol (B : Mat) (p v r : Cov) (L : Mat) : Mat := fun a b =>
  (∑ i, raiseCovector B v i * r i) * L a b +
    pureGauge p (fun d => ∑ i, raiseCovector B v i * L i d) a b

theorem lieTensorSymbol_symmetric (B : Mat) (p v r : Cov) (L : Mat)
    (hL : IsSymmetricTensor L) : IsSymmetricTensor (lieTensorSymbol B p v r L) := by
  intro a b
  simp only [lieTensorSymbol, pureGauge, hL a b]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

theorem gammaCross_eta (X Y : Jet) :
    gammaCross eta X Y = ∑ b, etaSign b *
      connectionCross (christoffel eta X) (christoffel eta Y) b b := by
  simp [gammaCross, eta, Matrix.diagonal_apply]

theorem connectionVariation_eta (H : Mat) (X : Jet) (a b c : Fin 4) :
    connectionVariation eta H X a b c =
      ∑ d, (-(etaSign a * H a d * etaSign d)) * koszul X b c d := by
  simp only [connectionVariation, christoffel, inverseVariation_eta_entry]

theorem gammaCrossVariation_eta (H : Mat) (X Y : Jet) :
    gammaCrossVariation eta H X Y =
      (∑ b, ∑ c, (-(etaSign b * H b c * etaSign c)) *
        connectionCross (christoffel eta X) (christoffel eta Y) b c) +
      ∑ b, etaSign b * connectionCrossVariation
        (christoffel eta X) (connectionVariation eta H X)
        (christoffel eta Y) (connectionVariation eta H Y) b b := by
  simp only [gammaCrossVariation, inverseVariation_eta_entry, inverseMatrix_eta,
    Finset.sum_add_distrib]
  congr 1
  simp [eta, Matrix.diagonal_apply]

/-- The actual Fourier linear Einstein symbol in canonical Minkowski,
with ordered lower-component variation and two raised output indices. -/
def einsteinSymbolEta (p : Cov) (J : Mat) : Mat := fun a b =>
  etaSign a * etaSign b * ricciSymbol eta p J a b -
    (1 / 2) * eta a b * metricTrace eta (ricciSymbol eta p J)

def einsteinPairingEta (p : Cov) (J L : Mat) : ℝ :=
  ∑ a, ∑ b, L a b * einsteinSymbolEta p J a b

def calibrationTime : Cov := fun a => if a = 0 then 1 else 0

def calibrationScreen : Mat := Matrix.diagonal (fun a => if a = 1 then 1 else if a = 2 then -1 else 0)

theorem calibration_kinetic_coefficient :
    metricKineticCoefficient eta (planeJet calibrationTime calibrationScreen)
      (planeJet (-calibrationTime) calibrationScreen) = 1 := by
  simp only [metricKineticCoefficient, metricDensity_eta, inverseMatrix_eta,
    kineticCoefficient_eq_cross, gammaCross_eta, connectionCross, christoffel_eta,
    koszul, planeJet, calibrationTime, calibrationScreen, Matrix.diagonal_apply]
  simp [etaSign, calibrationTime, Fin.sum_univ_succ]
  all_goals norm_num

theorem calibration_fourier_hessian :
    principalHessianPairing eta calibrationTime calibrationScreen calibrationScreen = -1 := by
  rw [principalHessianPairing, calibration_kinetic_coefficient]

theorem calibration_einstein_pairing :
    einsteinPairingEta calibrationTime calibrationScreen calibrationScreen = -1 := by
  simp only [einsteinPairingEta, einsteinSymbolEta, ricciSymbol, symbolNorm, contracted,
    metricTrace, raiseCovector, eta, calibrationTime, calibrationScreen, Matrix.diagonal_apply]
  simp [etaSign, Fin.sum_univ_succ]
  all_goals norm_num

theorem principalHessianPairing_eta_eq_einstein (p : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L) :
    principalHessianPairing eta p J L = einsteinPairingEta p J L := by
  simp only [principalHessianPairing, metricKineticCoefficient, metricDensity_eta,
    inverseMatrix_eta, kineticCoefficient_eq_cross, one_mul, gammaCross_eta]
  simp only [connectionCross, christoffel_eta, koszul, planeJet, Pi.neg_apply]
  simp (config := { maxSteps := 20000000 }) [einsteinPairingEta, einsteinSymbolEta,
    ricciSymbol, symbolNorm, contracted, metricTrace, raiseCovector,
    eta, Matrix.diagonal_apply, etaSign, Fin.sum_univ_succ,
    hJ 1 0, hJ 2 0, hJ 3 0, hJ 2 1, hJ 3 1, hJ 3 2,
    hL 1 0, hL 2 0, hL 3 0, hL 2 1, hL 3 1, hL 3 2]
  ring


end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators
open Burnett.RicciSymbol
theorem principalHessianPairing_eta_eq_zero_of_ricci_kernel (p : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L)
    (hR : ∀ a b, ricciSymbol eta p J a b = 0) :
    principalHessianPairing eta p J L = 0 := by
  rw [principalHessianPairing_eta_eq_einstein p J L hJ hL]
  simp only [einsteinPairingEta, einsteinSymbolEta, hR, metricTrace, mul_zero,
    Finset.sum_const_zero, sub_zero]


end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

theorem ricciSymbol_eta_phase_of_tracefree_contracted (p : Cov) (J : Mat)
    (ht : metricTrace eta J = 0) (hq : ∀ b, contracted eta p J b = 0) (a b : Fin 4) :
    ricciSymbol eta p J a b = (symbolNorm eta p / 2) * J a b := by
  simp only [ricciSymbol, ht, hq, mul_zero, add_zero, sub_zero]
  ring

theorem einsteinSymbolEta_phase_of_tracefree_contracted (p : Cov) (J : Mat)
    (ht : metricTrace eta J = 0) (hq : ∀ b, contracted eta p J b = 0) (a b : Fin 4) :
    einsteinSymbolEta p J a b = (symbolNorm eta p / 2) * (etaSign a * etaSign b * J a b) := by
  have hr := ricciSymbol_eta_phase_of_tracefree_contracted p J ht hq
  have htrace : metricTrace eta (ricciSymbol eta p J) = 0 := by
    calc
      _ = (symbolNorm eta p / 2) * metricTrace eta J := by
        unfold metricTrace
        simp_rw [hr, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = 0 := by rw [ht, mul_zero]
  rw [einsteinSymbolEta, hr, htrace]
  ring

end Burnett.Analysis.TransportWardSymbol
