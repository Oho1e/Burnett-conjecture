import Burnett.Analysis.TransportWard.HessianPhase

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 20000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

theorem inverseVariation_add_metric_direction (G H K : Mat) (a b : Fin 4) :
    inverseVariation G (H + K) a b = inverseVariation G H a b + inverseVariation G K a b := by
  simp only [inverseVariation_apply, Matrix.add_apply, add_mul, mul_add,
    Finset.sum_add_distrib]
  ring

theorem inverseVariation_smul_metric_direction (G H : Mat) (s : ℝ) (a b : Fin 4) :
    inverseVariation G (s • H) a b = s * inverseVariation G H a b := by
  rw [inverseVariation_apply, inverseVariation_apply]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hs : (∑ i, ∑ j, inverseMatrix G a i * (s * H i j) * inverseMatrix G j b) =
      s * (∑ i, ∑ j, inverseMatrix G a i * H i j * inverseMatrix G j b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [hs]
  ring

theorem connectionVariation_add_metric_direction (G H K : Mat) (X : Jet) (a b c : Fin 4) :
    connectionVariation G (H + K) X a b c =
      connectionVariation G H X a b c + connectionVariation G K X a b c := by
  simp only [connectionVariation, christoffel, inverseVariation_add_metric_direction,
    add_mul, Finset.sum_add_distrib]

theorem connectionVariation_smul_metric_direction (G H : Mat) (s : ℝ) (X : Jet)
    (a b c : Fin 4) :
    connectionVariation G (s • H) X a b c = s * connectionVariation G H X a b c := by
  simp only [connectionVariation, christoffel, inverseVariation_smul_metric_direction,
    mul_assoc, Finset.mul_sum]

theorem traceVariation_add_metric_direction (G H K : Mat) :
    traceVariation G (H + K) = traceVariation G H + traceVariation G K := by
  simp only [traceVariation, Matrix.add_mul, Matrix.trace_add]

theorem traceVariation_smul_metric_direction (G H : Mat) (s : ℝ) :
    traceVariation G (s • H) = s * traceVariation G H := by
  simp only [traceVariation, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul]

theorem gammaCrossVariation_add_metric_direction (G H K : Mat) (X Y : Jet) :
    gammaCrossVariation G (H + K) X Y =
      gammaCrossVariation G H X Y + gammaCrossVariation G K X Y := by
  have hcv (b c : Fin 4) :
      connectionCrossVariation (christoffel (inverseMatrix G) X) (connectionVariation G (H + K) X)
        (christoffel (inverseMatrix G) Y) (connectionVariation G (H + K) Y) b c =
      connectionCrossVariation (christoffel (inverseMatrix G) X) (connectionVariation G H X)
        (christoffel (inverseMatrix G) Y) (connectionVariation G H Y) b c +
      connectionCrossVariation (christoffel (inverseMatrix G) X) (connectionVariation G K X)
        (christoffel (inverseMatrix G) Y) (connectionVariation G K Y) b c := by
    unfold connectionCrossVariation
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e he
    simp only [connectionVariation_add_metric_direction]
    ring
  simp only [gammaCrossVariation, inverseVariation_add_metric_direction, hcv, add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  ring

theorem gammaCrossVariation_smul_metric_direction (G H : Mat) (s : ℝ) (X Y : Jet) :
    gammaCrossVariation G (s • H) X Y = s * gammaCrossVariation G H X Y := by
  have hcv (b c : Fin 4) :
      connectionCrossVariation (christoffel (inverseMatrix G) X) (connectionVariation G (s • H) X)
        (christoffel (inverseMatrix G) Y) (connectionVariation G (s • H) Y) b c =
      s * connectionCrossVariation (christoffel (inverseMatrix G) X) (connectionVariation G H X)
        (christoffel (inverseMatrix G) Y) (connectionVariation G H Y) b c := by
    unfold connectionCrossVariation
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    simp only [connectionVariation_smul_metric_direction]
    ring
  simp only [gammaCrossVariation, inverseVariation_smul_metric_direction, hcv]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem principalLeg_add_metric_direction (G H K : Mat) (hG : Matrix.det G ≠ 0) (X Y : Jet) :
    principalLeg G (H + K) X Y = principalLeg G H X Y + principalLeg G K X Y := by
  simp only [principalLeg_eq_cross_variation G _ hG,
    traceVariation_add_metric_direction, gammaCrossVariation_add_metric_direction]
  ring

theorem principalLeg_smul_metric_direction (G H : Mat) (hG : Matrix.det G ≠ 0)
    (s : ℝ) (X Y : Jet) :
    principalLeg G (s • H) X Y = s * principalLeg G H X Y := by
  simp only [principalLeg_eq_cross_variation G _ hG,
    traceVariation_smul_metric_direction, gammaCrossVariation_smul_metric_direction]
  ring

theorem koszul_smul_jet (s : ℝ) (X : Jet) (b c d : Fin 4) :
    koszul (s • X) b c d = s * koszul X b c d := by
  simp only [koszul, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem christoffel_smul_jet (B : Mat) (s : ℝ) (X : Jet) :
    christoffel B (s • X) = s • christoffel B X := by
  funext a b c
  simp only [christoffel, koszul_smul_jet, Pi.smul_apply, smul_eq_mul,
    mul_left_comm (_ : ℝ) s, Finset.mul_sum]

theorem connectionCross_smul_left (C D : Conn) (s : ℝ) (b c : Fin 4) :
    connectionCross (s • C) D b c = s * connectionCross C D b c := by
  unfold connectionCross
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem connectionCross_smul_right (C D : Conn) (s : ℝ) (b c : Fin 4) :
    connectionCross C (s • D) b c = s * connectionCross C D b c := by
  unfold connectionCross
  simp only [Pi.smul_apply, smul_eq_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem gammaCross_smul_left (B : Mat) (X Y : Jet) (s : ℝ) :
    gammaCross B (s • X) Y = s * gammaCross B X Y := by
  simp only [gammaCross, christoffel_smul_jet, connectionCross_smul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem gammaCross_smul_right (B : Mat) (X Y : Jet) (s : ℝ) :
    gammaCross B X (s • Y) = s * gammaCross B X Y := by
  simp only [gammaCross, christoffel_smul_jet, connectionCross_smul_right, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  ring

theorem kineticCoefficient_smul_left (B : Mat) (X Y : Jet) (s : ℝ) :
    kineticCoefficient B (s • X) Y = s * kineticCoefficient B X Y := by
  simp only [kineticCoefficient_eq_cross, gammaCross_smul_left, gammaCross_smul_right]
  ring

theorem kineticCoefficient_smul_right (B : Mat) (X Y : Jet) (s : ℝ) :
    kineticCoefficient B X (s • Y) = s * kineticCoefficient B X Y := by
  simp only [kineticCoefficient_eq_cross, gammaCross_smul_left, gammaCross_smul_right]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol

theorem principalLeg_add_left_jet (G H : Mat) (hG : Matrix.det G ≠ 0) (X Y Z : Jet) :
    principalLeg G H (X + Y) Z = principalLeg G H X Z + principalLeg G H Y Z := by
  have hfun : (fun t : ℝ => metricKineticCoefficient (G + t • H) (X + Y) Z) =
      (fun t : ℝ => metricKineticCoefficient (G + t • H) X Z +
        metricKineticCoefficient (G + t • H) Y Z) := by
    funext t
    simp only [metricKineticCoefficient, kineticCoefficient_add_left, mul_add]
  have hd := hasDerivAt_metricKineticCoefficient_path G H hG (X + Y) Z
  rw [hfun] at hd
  exact hd.unique ((hasDerivAt_metricKineticCoefficient_path G H hG X Z).add
    (hasDerivAt_metricKineticCoefficient_path G H hG Y Z))

theorem principalLeg_add_right_jet (G H : Mat) (hG : Matrix.det G ≠ 0) (X Y Z : Jet) :
    principalLeg G H X (Y + Z) = principalLeg G H X Y + principalLeg G H X Z := by
  have hfun : (fun t : ℝ => metricKineticCoefficient (G + t • H) X (Y + Z)) =
      (fun t : ℝ => metricKineticCoefficient (G + t • H) X Y +
        metricKineticCoefficient (G + t • H) X Z) := by
    funext t
    simp only [metricKineticCoefficient, kineticCoefficient_add_right, mul_add]
  have hd := hasDerivAt_metricKineticCoefficient_path G H hG X (Y + Z)
  rw [hfun] at hd
  exact hd.unique ((hasDerivAt_metricKineticCoefficient_path G H hG X Y).add
    (hasDerivAt_metricKineticCoefficient_path G H hG X Z))

theorem principalLeg_smul_left_jet (G H : Mat) (hG : Matrix.det G ≠ 0)
    (X Y : Jet) (s : ℝ) :
    principalLeg G H (s • X) Y = s * principalLeg G H X Y := by
  have hfun : (fun t : ℝ => metricKineticCoefficient (G + t • H) (s • X) Y) =
      (fun t : ℝ => s * metricKineticCoefficient (G + t • H) X Y) := by
    funext t
    simp only [metricKineticCoefficient, kineticCoefficient_smul_left]
    ring
  have hd := hasDerivAt_metricKineticCoefficient_path G H hG (s • X) Y
  rw [hfun] at hd
  exact hd.unique ((hasDerivAt_metricKineticCoefficient_path G H hG X Y).const_mul s)

theorem principalLeg_smul_right_jet (G H : Mat) (hG : Matrix.det G ≠ 0)
    (X Y : Jet) (s : ℝ) :
    principalLeg G H X (s • Y) = s * principalLeg G H X Y := by
  have hfun : (fun t : ℝ => metricKineticCoefficient (G + t • H) X (s • Y)) =
      (fun t : ℝ => s * metricKineticCoefficient (G + t • H) X Y) := by
    funext t
    simp only [metricKineticCoefficient, kineticCoefficient_smul_right]
    ring
  have hd := hasDerivAt_metricKineticCoefficient_path G H hG X (s • Y)
  rw [hfun] at hd
  exact hd.unique ((hasDerivAt_metricKineticCoefficient_path G H hG X Y).const_mul s)

theorem planeJet_add_amplitude (p : Cov) (H K : Mat) :
    planeJet p (H + K) = planeJet p H + planeJet p K := by
  funext a b c
  simp only [planeJet, Matrix.add_apply, Pi.add_apply, mul_add]

theorem planeJet_smul_amplitude (p : Cov) (H : Mat) (s : ℝ) :
    planeJet p (s • H) = s • planeJet p H := by
  funext a b c
  simp only [planeJet, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem planeJet_smul_covector (p : Cov) (H : Mat) (s : ℝ) :
    planeJet (s • p) H = s • planeJet p H := by
  funext a b c
  simp only [planeJet, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem principalVertex_add_first_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H K : Mat) (q : Cov) (J : Mat) (r : Cov) (L : Mat) :
    principalVertex G p (H + K) q J r L =
      principalVertex G p H q J r L + principalVertex G p K q J r L := by
  simp only [principalVertex, planeJet_add_amplitude,
    principalLeg_add_metric_direction G _ _ hG,
    principalLeg_add_left_jet G _ hG ]
  ring

theorem principalVertex_smul_first_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : Mat) (q : Cov) (J : Mat) (r : Cov) (L : Mat) (s : ℝ) :
    principalVertex G p (s • H) q J r L = s * principalVertex G p H q J r L := by
  simp only [principalVertex, planeJet_smul_amplitude,
    principalLeg_smul_metric_direction G _ hG,
    principalLeg_smul_left_jet G _ hG ]
  ring

theorem principalVertex_add_second_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : Mat) (q : Cov) (J K : Mat) (r : Cov) (L : Mat) :
    principalVertex G p H q (J + K) r L =
      principalVertex G p H q J r L + principalVertex G p H q K r L := by
  rw [principalVertex_swap_first_two G p H q (J + K) r L,
    principalVertex_add_first_amplitude G hG,
    principalVertex_swap_first_two G q J p H r L,
    principalVertex_swap_first_two G q K p H r L]

theorem principalVertex_smul_second_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : Mat) (q : Cov) (J : Mat) (r : Cov) (L : Mat) (s : ℝ) :
    principalVertex G p H q (s • J) r L = s * principalVertex G p H q J r L := by
  rw [principalVertex_swap_first_two G p H q (s • J) r L,
    principalVertex_smul_first_amplitude G hG,
    principalVertex_swap_first_two G q J p H r L]

theorem principalVertex_add_third_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : Mat) (q : Cov) (J : Mat) (r : Cov) (L K : Mat) :
    principalVertex G p H q J r (L + K) =
      principalVertex G p H q J r L + principalVertex G p H q J r K := by
  rw [principalVertex_cyclic G p H q J r (L + K),
    principalVertex_add_second_amplitude G hG,
    ←principalVertex_cyclic G p H q J r L,
    ←principalVertex_cyclic G p H q J r K]

theorem principalVertex_smul_third_amplitude (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : Mat) (q : Cov) (J : Mat) (r : Cov) (L : Mat) (s : ℝ) :
    principalVertex G p H q J r (s • L) = s * principalVertex G p H q J r L := by
  rw [principalVertex_cyclic G p H q J r (s • L),
    principalVertex_smul_second_amplitude G hG,
    ←principalVertex_cyclic G p H q J r L]

theorem principalVertex_frequency_homogeneity (G : Mat) (hG : Matrix.det G ≠ 0)
    (p q r : Cov) (H J L : Mat) (s : ℝ) :
    principalVertex G (s • p) H (s • q) J (s • r) L =
      s ^ 2 * principalVertex G p H q J r L := by
  simp only [principalVertex, planeJet_smul_covector,
    principalLeg_smul_left_jet G _ hG, principalLeg_smul_right_jet G _ hG]
  ring

end Burnett.Analysis.TransportWardSymbol
