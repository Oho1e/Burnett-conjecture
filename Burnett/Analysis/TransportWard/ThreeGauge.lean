import Burnett.Analysis.TransportWard.MetricVariation

set_option autoImplicit false
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

theorem koszul_add_jet (X Y : Jet) (b c d : Fin 4) :
    koszul (X + Y) b c d = koszul X b c d + koszul Y b c d := by
  simp only [koszul, Pi.add_apply, Matrix.add_apply]
  ring

theorem christoffel_add_jet (B : Mat) (X Y : Jet) :
    christoffel B (X + Y) = christoffel B X + christoffel B Y := by
  funext a b c
  simp only [christoffel, koszul_add_jet, mul_add, Finset.sum_add_distrib, Pi.add_apply]

def connectionCross (C D : Conn) (b c : Fin 4) : ℝ :=
  ∑ a, ∑ e, (C a a e * D e b c - C a c e * D e b a)

theorem quadraticDifference_add_connections (C D : Conn) (b c : Fin 4) :
    quadraticDifference (C + D) b c = quadraticDifference C b c +
      connectionCross C D b c + connectionCross D C b c + quadraticDifference D b c := by
  simp only [quadraticDifference, connectionCross, Pi.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  ring

def gammaCross (B : Mat) (X Y : Jet) : ℝ :=
  ∑ b, ∑ c, B b c * connectionCross (christoffel B X) (christoffel B Y) b c

theorem kineticCoefficient_eq_cross (B : Mat) (X Y : Jet) :
    kineticCoefficient B X Y = gammaCross B X Y + gammaCross B Y X := by
  simp only [kineticCoefficient, quadraticAction, christoffel_add_jet,
    quadraticDifference_add_connections, gammaCross, mul_add, Finset.sum_add_distrib]
  ring

theorem connectionCross_add_left (C D E : Conn) (b c : Fin 4) :
    connectionCross (C + D) E b c = connectionCross C E b c + connectionCross D E b c := by
  simp only [connectionCross, Pi.add_apply, add_mul, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem connectionCross_add_right (C D E : Conn) (b c : Fin 4) :
    connectionCross C (D + E) b c = connectionCross C D b c + connectionCross C E b c := by
  simp only [connectionCross, Pi.add_apply, mul_add, Finset.sum_add_distrib,
    Finset.sum_sub_distrib]
  ring

theorem gammaCross_add_left (B : Mat) (X Y Z : Jet) :
    gammaCross B (X + Y) Z = gammaCross B X Z + gammaCross B Y Z := by
  simp only [gammaCross, christoffel_add_jet, connectionCross_add_left, mul_add,
    Finset.sum_add_distrib]

theorem gammaCross_add_right (B : Mat) (X Y Z : Jet) :
    gammaCross B X (Y + Z) = gammaCross B X Y + gammaCross B X Z := by
  simp only [gammaCross, christoffel_add_jet, connectionCross_add_right, mul_add,
    Finset.sum_add_distrib]

theorem kineticCoefficient_add_left (B : Mat) (X Y Z : Jet) :
    kineticCoefficient B (X + Y) Z = kineticCoefficient B X Z + kineticCoefficient B Y Z := by
  simp only [kineticCoefficient_eq_cross, gammaCross_add_left, gammaCross_add_right]
  ring

theorem kineticCoefficient_add_right (B : Mat) (X Y Z : Jet) :
    kineticCoefficient B X (Y + Z) = kineticCoefficient B X Y + kineticCoefficient B X Z := by
  simp only [kineticCoefficient_eq_cross, gammaCross_add_left, gammaCross_add_right]
  ring

def bilinearPair (B : Mat) (p q : Cov) : ℝ := ∑ a, ∑ b, B a b * p a * q b

def rankOneConnection (p u : Cov) : Conn := fun a b c => p b * p c * u a

theorem connectionCross_rankOne (p u q v : Cov) (b c : Fin 4) :
    connectionCross (rankOneConnection p u) (rankOneConnection q v) b c =
      q b * q c * (∑ a, p a * u a) * (∑ e, p e * v e) -
      q b * p c * (∑ a, q a * u a) * (∑ e, p e * v e) := by
  unfold connectionCross rankOneConnection
  simp only [Finset.sum_sub_distrib]
  congr 1 <;> simp only [Finset.mul_sum, Finset.sum_mul] <;> rw [Finset.sum_comm] <;>
    apply Finset.sum_congr rfl <;> intro a ha <;>
    apply Finset.sum_congr rfl <;> intro e he <;> ring

theorem contract_raised_eq_bilinearPair (B : Mat) (p v : Cov) :
    (∑ a, p a * raiseCovector B v a) = bilinearPair B p v := by
  simp only [raiseCovector, bilinearPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  ring

theorem weightedPair_factor (B : Mat) (p q : Cov) (s t : ℝ) :
    (∑ b, ∑ c, B b c * (p b * q c * s * t)) = bilinearPair B p q * s * t := by
  simp only [bilinearPair, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem gammaCross_pureGauge (B : Mat) (p v q w : Cov) :
    gammaCross B (planeJet p (pureGauge p v)) (planeJet q (pureGauge q w)) =
      bilinearPair B p v * bilinearPair B p w * bilinearPair B q q -
        bilinearPair B q p * bilinearPair B q v * bilinearPair B p w := by
  have hp : christoffel B (planeJet p (pureGauge p v)) = rankOneConnection p (raiseCovector B v) := by
    funext a b c
    exact christoffel_plane_pureGauge B p v a b c
  have hq : christoffel B (planeJet q (pureGauge q w)) = rankOneConnection q (raiseCovector B w) := by
    funext a b c
    exact christoffel_plane_pureGauge B q w a b c
  unfold gammaCross
  rw [hp, hq]
  simp_rw [connectionCross_rankOne, contract_raised_eq_bilinearPair]
  simp only [mul_sub, Finset.sum_sub_distrib]
  rw [weightedPair_factor, weightedPair_factor]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

def gaugeMatrix (p v : Cov) : Mat := pureGauge p v

def gaugeKineticScalar (B : Mat) (p v q w : Cov) : ℝ :=
  bilinearPair B p p * bilinearPair B q v * bilinearPair B q w +
    bilinearPair B q q * bilinearPair B p v * bilinearPair B p w -
    (bilinearPair B p q + bilinearPair B q p) * bilinearPair B q v * bilinearPair B p w

theorem kineticCoefficient_pureGauge (B : Mat) (p v q w : Cov) :
    kineticCoefficient B (planeJet p (pureGauge p v)) (planeJet q (pureGauge q w)) =
      gaugeKineticScalar B p v q w := by
  rw [kineticCoefficient_eq_cross, gammaCross_pureGauge, gammaCross_pureGauge]
  unfold gaugeKineticScalar
  ring

def etaPair (p q : Cov) : ℝ := bilinearPair eta p q

theorem etaPair_eq_sum (p q : Cov) :
    etaPair p q = ∑ a, etaSign a * p a * q a := by
  simp [etaPair, bilinearPair, eta, Matrix.diagonal_apply]

theorem etaPair_comm (p q : Cov) : etaPair p q = etaPair q p := by
  rw [etaPair_eq_sum, etaPair_eq_sum]
  apply Finset.sum_congr rfl
  intro a ha
  ring

theorem etaPair_add_left (p q r : Cov) : etaPair (p + q) r = etaPair p r + etaPair q r := by
  simp only [etaPair_eq_sum, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]

theorem etaPair_add_right (p q r : Cov) : etaPair p (q + r) = etaPair p q + etaPair p r := by
  simp only [etaPair_eq_sum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem etaPair_neg_left (p q : Cov) : etaPair (-p) q = -etaPair p q := by
  simp only [etaPair_eq_sum, Pi.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]

theorem etaPair_neg_right (p q : Cov) : etaPair p (-q) = -etaPair p q := by
  simp only [etaPair_eq_sum, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]

theorem etaPair_product (p q r s : Cov) :
    etaPair p q * etaPair r s =
      ∑ a, ∑ b, (etaSign a * p a * q a) * (etaSign b * r b * s b) := by
  rw [etaPair_eq_sum, etaPair_eq_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]

theorem inverseVariation_eta_entry (H : Mat) (a b : Fin 4) :
    inverseVariation eta H a b = -(etaSign a * H a b * etaSign b) := by
  change -((inverseMatrix eta * H * inverseMatrix eta) a b) = _
  have hi : inverseMatrix eta = eta := matrixInverse_eta
  rw [hi]
  simp [eta, Matrix.mul_apply, Matrix.diagonal_apply]

theorem bilinearPair_inverseVariation_eta_pureGauge (k z x y : Cov) :
    bilinearPair (inverseVariation eta (pureGauge k z)) x y =
      -(etaPair x k * etaPair z y + etaPair x z * etaPair k y) := by
  calc
    _ = ∑ a, ∑ b, (-(etaSign a * x a * k a) * (etaSign b * z b * y b) -
        (etaSign a * x a * z a) * (etaSign b * k b * y b)) := by
      unfold bilinearPair
      apply Finset.sum_congr rfl
      intro a ha
      apply Finset.sum_congr rfl
      intro b hb
      rw [inverseVariation_eta_entry]
      simp only [pureGauge]
      ring
    _ = _ := by
      rw [etaPair_product, etaPair_product]
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib, neg_mul]
      ring

theorem traceVariation_eta (H : Mat) : traceVariation eta H = ∑ a, etaSign a * H a a := by
  have hi : inverseMatrix eta = eta := matrixInverse_eta
  rw [traceVariation, hi]
  simp [Matrix.trace, Matrix.mul_apply, eta, Matrix.diagonal_apply, mul_comm]

theorem traceVariation_eta_pureGauge (k z : Cov) :
    traceVariation eta (pureGauge k z) = 2 * etaPair k z := by
  rw [traceVariation_eta, etaPair_eq_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [pureGauge]
  ring

def metricPair (G : Mat) (x y : Cov) : ℝ := bilinearPair (inverseMatrix G) x y

theorem metricPair_eta (x y : Cov) : metricPair eta x y = etaPair x y := by
  unfold metricPair etaPair
  congr 1
  exact matrixInverse_eta

theorem hasDerivAt_metricPair_path (G H : Mat) (hG : Matrix.det G ≠ 0) (x y : Cov) :
    HasDerivAt (fun t : ℝ => metricPair (G + t • H) x y)
      (bilinearPair (inverseVariation G H) x y) 0 := by
  simpa only [metricPair, bilinearPair] using
    HasDerivAt.fun_sum (fun a _ => HasDerivAt.fun_sum (fun b _ =>
      ((hasDerivAt_inverseMatrix_entry_path G H hG a b).mul_const (x a)).mul_const (y b)))

theorem hasDerivAt_metricPair_pureGauge_eta (k z x y : Cov) :
    HasDerivAt (fun t : ℝ => metricPair (eta + t • gaugeMatrix k z) x y)
      (-(etaPair x k * etaPair z y + etaPair x z * etaPair k y)) 0 := by
  simpa only [bilinearPair_inverseVariation_eta_pureGauge] using
    hasDerivAt_metricPair_path eta (pureGauge k z)
      (det_ne_zero_of_right_inverse eta eta eta_mul_eta) x y

theorem hasDerivAt_metricDensity_pureGauge_eta (k z : Cov) :
    HasDerivAt (fun t : ℝ => metricDensity (eta + t • gaugeMatrix k z)) (etaPair k z) 0 := by
  convert hasDerivAt_metricDensity_path eta (pureGauge k z)
    (det_ne_zero_of_right_inverse eta eta eta_mul_eta) using 1
  rw [metricDensity_eta, traceVariation_eta_pureGauge]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

def gaugeMetricScalar (G : Mat) (p v q w : Cov) : ℝ :=
  metricPair G p p * metricPair G q v * metricPair G q w +
    metricPair G q q * metricPair G p v * metricPair G p w -
    (metricPair G p q + metricPair G q p) * metricPair G q v * metricPair G p w

theorem metricKineticCoefficient_pureGauge (G : Mat) (p v q w : Cov) :
    metricKineticCoefficient G (planeJet p (pureGauge p v)) (planeJet q (pureGauge q w)) =
      metricDensity G * gaugeMetricScalar G p v q w := by
  rw [metricKineticCoefficient, kineticCoefficient_pureGauge]
  rfl

def etaGaugeKinetic (p v q w : Cov) : ℝ :=
  etaPair p p * etaPair q v * etaPair q w + etaPair q q * etaPair p v * etaPair p w -
    (etaPair p q + etaPair q p) * etaPair q v * etaPair p w

theorem gaugeMetricScalar_eta (p v q w : Cov) :
    gaugeMetricScalar eta p v q w = etaGaugeKinetic p v q w := by
  simp only [gaugeMetricScalar, metricPair_eta, etaGaugeKinetic]

def etaPairVariation (k z x y : Cov) : ℝ :=
  -(etaPair x k * etaPair z y + etaPair x z * etaPair k y)

def etaGaugeKineticVariation (k z p v q w : Cov) : ℝ :=
  ((etaPairVariation k z p p * etaPair q v + etaPair p p * etaPairVariation k z q v) * etaPair q w +
    etaPair p p * etaPair q v * etaPairVariation k z q w) +
  ((etaPairVariation k z q q * etaPair p v + etaPair q q * etaPairVariation k z p v) * etaPair p w +
    etaPair q q * etaPair p v * etaPairVariation k z p w) -
  (((etaPairVariation k z p q + etaPairVariation k z q p) * etaPair q v +
    (etaPair p q + etaPair q p) * etaPairVariation k z q v) * etaPair p w +
      (etaPair p q + etaPair q p) * etaPair q v * etaPairVariation k z p w)

def gaugeCubicLegPolynomial (k z p v q w : Cov) : ℝ :=
  etaPair k z * etaGaugeKinetic p v q w + etaGaugeKineticVariation k z p v q w

theorem hasDerivAt_gaugeMetricScalar_pureGauge_eta (k z p v q w : Cov) :
    HasDerivAt (fun t : ℝ => gaugeMetricScalar (eta + t • gaugeMatrix k z) p v q w)
      (etaGaugeKineticVariation k z p v q w) 0 := by
  have hd (x y : Cov) := hasDerivAt_metricPair_pureGauge_eta k z x y
  have hs := ((((hd p p).mul (hd q v)).mul (hd q w)).add
    (((hd q q).mul (hd p v)).mul (hd p w))).sub
      ((((hd p q).add (hd q p)).mul (hd q v)).mul (hd p w))
  simpa only [gaugeMetricScalar, etaGaugeKineticVariation, etaPairVariation,
    Pi.mul_apply, Pi.add_apply, zero_smul, add_zero, metricPair_eta] using hs

theorem principalLeg_eta_three_gauge_identification (k z p v q w : Cov) :
    principalLeg eta (pureGauge k z) (planeJet p (pureGauge p v)) (planeJet q (pureGauge q w)) =
      gaugeCubicLegPolynomial k z p v q w := by
  have hs := (hasDerivAt_metricDensity_pureGauge_eta k z).mul
    (hasDerivAt_gaugeMetricScalar_pureGauge_eta k z p v q w)
  have ht : HasDerivAt
      (fun t : ℝ => metricKineticCoefficient (eta + t • gaugeMatrix k z)
        (planeJet p (pureGauge p v)) (planeJet q (pureGauge q w)))
      (gaugeCubicLegPolynomial k z p v q w) 0 := by
    simpa only [metricKineticCoefficient_pureGauge, zero_smul, add_zero,
      metricDensity_eta, gaugeMetricScalar_eta, one_mul, gaugeCubicLegPolynomial] using hs
  exact (hasDerivAt_metricKineticCoefficient_path eta (pureGauge k z)
    (det_ne_zero_of_right_inverse eta eta eta_mul_eta) _ _).unique ht

theorem gaugeCubicLegPolynomial_conserved_sum (p v q w z : Cov) :
    gaugeCubicLegPolynomial p v q w (-(p + q)) z +
      gaugeCubicLegPolynomial q w p v (-(p + q)) z +
      gaugeCubicLegPolynomial (-(p + q)) z p v q w = 0 := by
  unfold gaugeCubicLegPolynomial etaGaugeKinetic etaGaugeKineticVariation etaPairVariation
  simp only [etaPair_neg_left, etaPair_neg_right, etaPair_add_left, etaPair_add_right]
  simp only [etaPair_comm q p, etaPair_comm v p, etaPair_comm w p, etaPair_comm z p,
    etaPair_comm v q, etaPair_comm w q, etaPair_comm z q, etaPair_comm w v,
    etaPair_comm z v, etaPair_comm z w]
  ring

/-- The true constructed cubic coefficient vanishes on three pure gauges
for every conserved signed triad over canonical Minkowski. No null assumption. -/
theorem principalVertex_eta_three_pureGauge (p q r v w z : Cov)
    (hcon : ∀ a, p a + q a + r a = 0) :
    principalVertex eta p (pureGauge p v) q (pureGauge q w) r (pureGauge r z) = 0 := by
  have hr : r = -(p + q) := by
    funext a
    have h := hcon a
    simp only [Pi.neg_apply, Pi.add_apply]
    linarith
  subst r
  simp only [principalVertex, principalLeg_eta_three_gauge_identification]
  rw [gaugeCubicLegPolynomial_conserved_sum, neg_zero]

end Burnett.Analysis.TransportWardSymbol
