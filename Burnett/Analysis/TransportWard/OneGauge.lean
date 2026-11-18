import Burnett.Analysis.TransportWard.HessianPhase

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 20000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

theorem connectionVariation_plane_pureGauge (G H : Mat) (p v : Cov) (a b c : Fin 4) :
    connectionVariation G H (planeJet p (pureGauge p v)) a b c =
      p b * p c * raiseCovector (inverseVariation G H) v a := by
  exact christoffel_plane_pureGauge (inverseVariation G H) p v a b c

theorem principalVertex_eta_one_pureGauge_ward (p q r v : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L)
    (hcon : ∀ a, p a + q a + r a = 0) :
    principalVertex eta p (pureGauge p v) q J r L =
      -principalHessianPairing eta q J (lieTensorSymbol eta p v r L) -
        principalHessianPairing eta r L (lieTensorSymbol eta p v q J) := by
  rw [principalHessianPairing_eta_eq_einstein q J _ hJ (lieTensorSymbol_symmetric eta p v r L hL),
    principalHessianPairing_eta_eq_einstein r L _ hL (lieTensorSymbol_symmetric eta p v q J hJ)]
  have hr : r = -(p + q) := by
    funext a
    have h := hcon a
    simp only [Pi.neg_apply, Pi.add_apply]
    linarith
  subst r
  simp only [principalVertex, principalLeg_eta_eq_cross_variation,
    gammaCross_eta, gammaCrossVariation_eta, traceVariation_eta]
  simp only [connectionCross, connectionCrossVariation]
  simp only [christoffel_plane_pureGauge, connectionVariation_plane_pureGauge]
  simp only [christoffel_eta, connectionVariation_eta, koszul, planeJet, pureGauge]
  simp only [raiseCovector, inverseVariation_eta_entry]
  simp (config := { maxSteps := 20000000 }) [einsteinPairingEta, einsteinSymbolEta, ricciSymbol,
    symbolNorm, contracted, metricTrace, lieTensorSymbol, raiseCovector, pureGauge,
    eta, Matrix.diagonal_apply, etaSign, Fin.sum_univ_succ,
    hJ 1 0, hJ 2 0, hJ 3 0, hJ 2 1, hJ 3 1, hJ 3 2,
    hL 1 0, hL 2 0, hL 3 0, hL 2 1, hL 3 1, hL 3 2]
  ring


theorem principalVertex_eta_one_gauge_eq_zero_of_ricci_kernels (p q r v : Cov) (J L : Mat)
    (hJ : IsSymmetricTensor J) (hL : IsSymmetricTensor L)
    (hcon : ∀ a, p a + q a + r a = 0)
    (hRJ : ∀ a b, ricciSymbol eta q J a b = 0)
    (hRL : ∀ a b, ricciSymbol eta r L a b = 0) :
    principalVertex eta p (pureGauge p v) q J r L = 0 := by
  rw [principalVertex_eta_one_pureGauge_ward p q r v J L hJ hL hcon,
    principalHessianPairing_eta_eq_zero_of_ricci_kernel q J _ hJ
      (lieTensorSymbol_symmetric eta p v r L hL) hRJ,
    principalHessianPairing_eta_eq_zero_of_ricci_kernel r L _ hL
      (lieTensorSymbol_symmetric eta p v q J hJ) hRL]
  ring


end Burnett.Analysis.TransportWardSymbol
