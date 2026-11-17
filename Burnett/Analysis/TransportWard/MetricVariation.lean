import Burnett.Geometry.InverseField
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Topology.Instances.Matrix
import Mathlib.Analysis.Calculus.Deriv.Add
import Burnett.Geometry.CurvatureDifference

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8000
set_option synthInstance.maxHeartbeats 200000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology Matrix.Norms.Elementwise
open Burnett.RicciSymbol Burnett.Geometry.InverseField
abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
abbrev Cov := Fin 4 → ℝ
abbrev Jet := Fin 4 → Mat
abbrev Conn := Fin 4 → Fin 4 → Fin 4 → ℝ

def inverseMatrix (G : Mat) : Mat := matrixInverse G

def detMultilinear : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => Fin 4 → ℝ) ℝ :=
  { Matrix.detRowAlternating.toMultilinearMap with cont := continuous_id.matrix_det }

theorem hasDerivAt_det_path (G H : Mat) :
    HasDerivAt (fun t : ℝ => Matrix.det (G + t • H))
      (∑ i, Matrix.det (Function.update G i (H i))) 0 := by
  have hd := detMultilinear.hasFDerivAt G
  have hp : HasDerivAt (fun t : ℝ => G + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add G
  have hd0 : HasFDerivAt detMultilinear (detMultilinear.linearDeriv G) (G + (0 : ℝ) • H) := by
    simpa using hd
  convert hd0.comp_hasDerivAt 0 hp using 1

def traceVariation (G H : Mat) : ℝ := Matrix.trace ((H * (inverseMatrix G) : Mat))

theorem det_updateRow_eq_traceTerm (G H : Mat) (hG : Matrix.det G ≠ 0) (i : Fin 4) :
    Matrix.det (Function.update G i (H i)) =
      ((H * (inverseMatrix G) : Mat)) i i * Matrix.det G := by
  have hm : ((H * (inverseMatrix G)) * G : Mat) = H := by
    have hi : ((inverseMatrix G) * G : Mat) = 1 := matrixInverse_compose G hG
    rw [Matrix.mul_assoc, hi, Matrix.mul_one]
  have hr : (∑ k, ((H * (inverseMatrix G) : Mat)) i k • G k) = H i := by
    funext j
    change (∑ k, ((H * (inverseMatrix G) : Mat)) i k * G k j) = H i j
    exact congrFun (congrFun hm i) j
  have ht := Matrix.det_updateRow_sum G i (((H * (inverseMatrix G) : Mat)) i)
  rw [hr] at ht
  exact ht

theorem hasDerivAt_det_path_of_nonsingular (G H : Mat) (hG : Matrix.det G ≠ 0) :
    HasDerivAt (fun t : ℝ => Matrix.det (G + t • H))
      (Matrix.det G * traceVariation G H) 0 := by
  convert hasDerivAt_det_path G H using 1
  simp only [det_updateRow_eq_traceTerm G H hG]
  dsimp [traceVariation, Matrix.trace, Matrix.diag]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

def metricDensity (G : Mat) : ℝ := Real.sqrt |Matrix.det G|

theorem hasDerivAt_metricDensity_path (G H : Mat) (hG : Matrix.det G ≠ 0) :
    HasDerivAt (fun t : ℝ => metricDensity (G + t • H))
      (metricDensity G / 2 * traceVariation G H) 0 := by
  have hd := hasDerivAt_det_path_of_nonsingular G H hG
  have ha0 : HasDerivAt (fun x : ℝ => |x|) (SignType.sign (Matrix.det G) : ℝ)
      (Matrix.det (G + (0 : ℝ) • H)) := by simpa using hasDerivAt_abs hG
  have habs := ha0.comp 0 hd
  have hs0 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt |Matrix.det G|))
      |Matrix.det (G + (0 : ℝ) • H)| := by
    simpa using Real.hasDerivAt_sqrt (abs_ne_zero.mpr hG)
  have hs := hs0.comp 0 habs
  convert hs using 1
  have hpos : 0 < Real.sqrt |Matrix.det G| := Real.sqrt_pos.2 (abs_pos.mpr hG)
  have hsq := Real.sq_sqrt (abs_nonneg (Matrix.det G))
  have hsign : (SignType.sign (Matrix.det G) : ℝ) * Matrix.det G = |Matrix.det G| :=
    sign_mul_self _
  have hsd : (SignType.sign (Matrix.det G) : ℝ) * (Matrix.det G * traceVariation G H) =
      |Matrix.det G| * traceVariation G H := by rw [← mul_assoc, hsign]
  dsimp [metricDensity]
  rw [hsd]
  field_simp [ne_of_gt hpos]
  rw [hsq]
  ring

end Burnett.Analysis.TransportWardSymbol

namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
section OperatorNormOnly
open scoped Matrix.Norms.Operator

theorem hasDerivAt_matrixInverse_entry_path (G H : Mat) (hG : Matrix.det G ≠ 0)
    (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => matrixInverse (G + t • H) a b)
      (-(inverseMatrix G * H * inverseMatrix G : Mat) a b) 0 := by
  have hU : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).mpr (isUnit_iff_ne_zero.mpr hG)
  obtain ⟨u, hu⟩ := hU
  let ev : Mat →L[ℝ] ℝ := LinearMap.toContinuousLinearMap
    { toFun := fun A => A a b
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hp : HasDerivAt (fun t : ℝ => G + t • H) H 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const H).const_add G
  have hir := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hir
  have hir0 : HasFDerivAt Ring.inverse (-ContinuousLinearMap.mulLeftRight ℝ Mat (↑u⁻¹) (↑u⁻¹))
      (G + (0 : ℝ) • H) := by simpa using hir
  have hi := hir0.comp_hasDerivAt 0 hp
  have ht := ev.hasFDerivAt.comp_hasDerivAt 0 hi
  have hui : ((↑u⁻¹) : Mat) = inverseMatrix G := by
    change ((↑u⁻¹) : Mat) = (G⁻¹ : Mat)
    rw [Matrix.nonsing_inv_eq_ringInverse, ← hu, Ring.inverse_unit]
  change HasDerivAt (fun t : ℝ => Ring.inverse (G + t • H) a b)
    ((-((↑u⁻¹ : Mat) * H * ↑u⁻¹) : Mat) a b) 0 at ht
  rw [hui] at ht
  simpa only [inverseMatrix, matrixInverse, Matrix.nonsing_inv_eq_ringInverse, Pi.neg_apply] using ht

end OperatorNormOnly
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
set_option maxRecDepth 16000
set_option maxHeartbeats 4000000
def planeJet (p : Cov) (H : Mat) : Jet := fun a b c => p a * H b c

theorem christoffel_plane (B : Mat) (p : Cov) (H : Mat) (hH : IsSymmetricTensor H)
    (a b c : Fin 4) :
    christoffel B (planeJet p H) a b c = connectionSymbol B p H a b c := by
  simp only [christoffel, koszul, planeJet, connectionSymbol, raiseSecond, raiseCovector]
  simp_rw [hH b _, hH c _]
  simp [Fin.sum_univ_succ]
  ring

theorem christoffel_plane_pureGauge (B : Mat) (p v : Cov) (a b c : Fin 4) :
    christoffel B (planeJet p (pureGauge p v)) a b c = p b * p c * raiseCovector B v a := by
  rw [christoffel_plane B p (pureGauge p v) (by intro i j; simp [pureGauge]; ring)]
  exact connectionSymbol_pureGauge B p v a b c

/-- The actual quadratic first-order -R density before its volume factor.
The connection is built from the inverse metric and the actual metric jet. -/
def quadraticAction (B : Mat) (X : Jet) : ℝ :=
  ∑ b, ∑ c, B b c * quadraticDifference (christoffel B X) b c

/-- Exact cross coefficient of the quadratic Gamma-Gamma expression. -/
def kineticCoefficient (B : Mat) (X Y : Jet) : ℝ :=
  quadraticAction B (X + Y) - quadraticAction B X - quadraticAction B Y

def etaSign (i : Fin 4) : ℝ := if i = 0 then -1 else 1

def eta : Mat := Matrix.diagonal etaSign

theorem eta_mul_eta : (eta * eta : Mat) = 1 := by
  rw [eta, Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    by_cases hi : i = 0 <;> simp [etaSign, hi]
  · simp [hij]

theorem matrixInverse_eta : matrixInverse eta = eta :=
  matrixInverse_eq_of_right_inverse eta eta eta_mul_eta

theorem christoffel_eta (X : Jet) (a b c : Fin 4) :
    christoffel eta X a b c = etaSign a * koszul X b c a := by
  simp [christoffel, eta, Matrix.diagonal_apply]

theorem quadraticAction_eta (X : Jet) :
    quadraticAction eta X = ∑ b, etaSign b * quadraticDifference (christoffel eta X) b b := by
  simp [quadraticAction, eta, Matrix.diagonal_apply]

/-- A genuine off-shell gauge kernel statement for the Gamma-Gamma Hessian.
No null-covector hypothesis is imposed. -/
theorem kinetic_eta_plane_pureGauge (p v : Cov) (J : Mat) (hJ : IsSymmetricTensor J) :
    kineticCoefficient eta (planeJet p (pureGauge p v)) (planeJet (-p) J) = 0 := by
  simp only [kineticCoefficient, quadraticAction_eta, quadraticDifference, christoffel_eta]
  simp (config := { maxSteps := 10000000 }) [koszul, planeJet, pureGauge,
    etaSign, Fin.sum_univ_succ, hJ 1 0, hJ 2 0, hJ 3 0, hJ 2 1, hJ 3 1, hJ 3 2]
  ring


end Burnett.Analysis.TransportWardSymbol

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1000000
noncomputable section
namespace Burnett.Analysis.TransportWardSymbol
open scoped BigOperators Topology
open Burnett.RicciSymbol Burnett.Geometry.InverseField
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference

def inverseVariation (G H : Mat) : Mat := -(inverseMatrix G * H * inverseMatrix G)

theorem inverseVariation_apply (G H : Mat) (a b : Fin 4) :
    inverseVariation G H a b = -∑ i, ∑ j,
      inverseMatrix G a i * H i j * inverseMatrix G j b := by
  change -((inverseMatrix G * H * inverseMatrix G) a b) = _
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]

def connectionVariation (G H : Mat) (X : Jet) : Conn :=
  christoffel (inverseVariation G H) X

theorem hasDerivAt_inverseMatrix_entry_path (G H : Mat) (hG : Matrix.det G ≠ 0)
    (a b : Fin 4) :
    HasDerivAt (fun t : ℝ => inverseMatrix (G + t • H) a b)
      (inverseVariation G H a b) 0 := by
  simpa only [inverseMatrix, inverseVariation, Pi.neg_apply] using
    hasDerivAt_matrixInverse_entry_path G H hG a b

theorem hasDerivAt_christoffel_inverse_path (G H : Mat) (hG : Matrix.det G ≠ 0)
    (X : Jet) (a b c : Fin 4) :
    HasDerivAt (fun t : ℝ => christoffel (inverseMatrix (G + t • H)) X a b c)
      (connectionVariation G H X a b c) 0 := by
  simpa only [christoffel, connectionVariation] using
    HasDerivAt.fun_sum (fun d _ =>
      (hasDerivAt_inverseMatrix_entry_path G H hG a d).mul_const (koszul X b c d))

def quadraticConnectionVariation (C DC : Conn) (b c : Fin 4) : ℝ :=
  ∑ a, ∑ e, ((DC a a e * C e b c + C a a e * DC e b c) -
    (DC a c e * C e b a + C a c e * DC e b a))

theorem hasDerivAt_quadraticDifference (C : ℝ → Conn) (DC : Conn)
    (hC : ∀ a b c, HasDerivAt (fun t => C t a b c) (DC a b c) 0)
    (b c : Fin 4) :
    HasDerivAt (fun t => quadraticDifference (C t) b c)
      (quadraticConnectionVariation (C 0) DC b c) 0 := by
  unfold quadraticDifference quadraticConnectionVariation
  exact HasDerivAt.fun_sum (fun a _ => HasDerivAt.fun_sum (fun e _ =>
    ((hC a a e).mul (hC e b c)).sub ((hC a c e).mul (hC e b a))))

def quadraticActionVariation (G H : Mat) (X : Jet) : ℝ :=
  ∑ b, ∑ c, (inverseVariation G H b c * quadraticDifference (christoffel (inverseMatrix G) X) b c +
    inverseMatrix G b c * quadraticConnectionVariation (christoffel (inverseMatrix G) X)
      (connectionVariation G H X) b c)

theorem hasDerivAt_quadraticAction_inverse_path (G H : Mat) (hG : Matrix.det G ≠ 0)
    (X : Jet) :
    HasDerivAt (fun t : ℝ => quadraticAction (inverseMatrix (G + t • H)) X)
      (quadraticActionVariation G H X) 0 := by
  have hC := hasDerivAt_christoffel_inverse_path G H hG X
  have hQ (b c : Fin 4) := hasDerivAt_quadraticDifference
    (fun t => christoffel (inverseMatrix (G + t • H)) X) (connectionVariation G H X) hC b c
  unfold quadraticAction quadraticActionVariation
  simpa only [zero_smul, add_zero] using
    HasDerivAt.fun_sum (fun b _ => HasDerivAt.fun_sum (fun c _ =>
      (hasDerivAt_inverseMatrix_entry_path G H hG b c).mul (hQ b c)))

/-- The actual first-order Gamma-Gamma density for S=-integral R sqrt|det|,
with the raw coordinate metric jet; no Ward expression occurs in its definition. -/
def metricActionDensity (G : Mat) (X : Jet) : ℝ :=
  metricDensity G * quadraticAction (inverseMatrix G) X

def actionDensityVariation (G H : Mat) (X : Jet) : ℝ :=
  (metricDensity G / 2 * traceVariation G H) * quadraticAction (inverseMatrix G) X +
    metricDensity G * quadraticActionVariation G H X

theorem hasDerivAt_metricActionDensity_path (G H : Mat) (hG : Matrix.det G ≠ 0)
    (X : Jet) :
    HasDerivAt (fun t : ℝ => metricActionDensity (G + t • H) X)
      (actionDensityVariation G H X) 0 := by
  simpa only [metricActionDensity, actionDensityVariation, zero_smul, add_zero] using
    (hasDerivAt_metricDensity_path G H hG).mul
      (hasDerivAt_quadraticAction_inverse_path G H hG X)

/-- Exact cross coefficient of the density, including the actual inverse and volume. -/
def metricKineticCoefficient (G : Mat) (X Y : Jet) : ℝ :=
  metricDensity G * kineticCoefficient (inverseMatrix G) X Y

theorem metricKineticCoefficient_eq_polarization (G : Mat) (X Y : Jet) :
    metricKineticCoefficient G X Y =
      metricActionDensity G (X + Y) - metricActionDensity G X - metricActionDensity G Y := by
  simp only [metricKineticCoefficient, kineticCoefficient, metricActionDensity]
  ring

/-- The undifferentiated metric leg of the cubic action coefficient. -/
def principalLeg (G H : Mat) (X Y : Jet) : ℝ :=
  actionDensityVariation G H (X + Y) - actionDensityVariation G H X - actionDensityVariation G H Y

theorem hasDerivAt_metricKineticCoefficient_path (G H : Mat) (hG : Matrix.det G ≠ 0)
    (X Y : Jet) :
    HasDerivAt (fun t : ℝ => metricKineticCoefficient (G + t • H) X Y)
      (principalLeg G H X Y) 0 := by
  simpa only [metricKineticCoefficient_eq_polarization, principalLeg] using
    ((hasDerivAt_metricActionDensity_path G H hG (X + Y)).sub
      (hasDerivAt_metricActionDensity_path G H hG X)).sub
        (hasDerivAt_metricActionDensity_path G H hG Y)

/-- Signed real Fourier coefficient of the principal cubic action.
The minus sign comes from the two Fourier coordinate derivatives i*p and i*q.
Momentum conservation is a separate hypothesis of future Ward statements. -/
def principalVertex (G : Mat) (p : Cov) (H : Mat) (q : Cov) (J : Mat)
    (r : Cov) (L : Mat) : ℝ :=
  -(principalLeg G H (planeJet q J) (planeJet r L) +
    principalLeg G J (planeJet p H) (planeJet r L) +
    principalLeg G L (planeJet p H) (planeJet q J))

theorem principalVertex_eq_actual_cyclic_variation (G : Mat) (hG : Matrix.det G ≠ 0)
    (p : Cov) (H : Mat) (q : Cov) (J : Mat) (r : Cov) (L : Mat) :
    principalVertex G p H q J r L =
      -(deriv (fun t : ℝ => metricKineticCoefficient (G + t • H) (planeJet q J) (planeJet r L)) 0 +
        deriv (fun t : ℝ => metricKineticCoefficient (G + t • J) (planeJet p H) (planeJet r L)) 0 +
        deriv (fun t : ℝ => metricKineticCoefficient (G + t • L) (planeJet p H) (planeJet q J)) 0) := by
  rw [(hasDerivAt_metricKineticCoefficient_path G H hG _ _).deriv,
    (hasDerivAt_metricKineticCoefficient_path G J hG _ _).deriv,
    (hasDerivAt_metricKineticCoefficient_path G L hG _ _).deriv]
  rfl

theorem principalLeg_comm (G H : Mat) (X Y : Jet) :
    principalLeg G H X Y = principalLeg G H Y X := by
  simp only [principalLeg, add_comm X Y]
  ring

theorem principalVertex_swap_first_two (G : Mat) (p : Cov) (H : Mat) (q : Cov)
    (J : Mat) (r : Cov) (L : Mat) :
    principalVertex G p H q J r L = principalVertex G q J p H r L := by
  simp only [principalVertex, principalLeg_comm G L (planeJet q J) (planeJet p H)]
  ring

theorem principalVertex_cyclic (G : Mat) (p : Cov) (H : Mat) (q : Cov)
    (J : Mat) (r : Cov) (L : Mat) :
    principalVertex G p H q J r L = principalVertex G q J r L p H := by
  simp only [principalVertex, principalLeg_comm G J (planeJet r L) (planeJet p H),
    principalLeg_comm G L (planeJet q J) (planeJet p H)]
  ring

theorem metricDensity_eta : metricDensity eta = 1 := by
  norm_num [metricDensity, eta, Matrix.det_diagonal, etaSign, Fin.prod_univ_succ]

theorem metricKineticCoefficient_eta_pureGauge (p v : Cov) (J : Mat)
    (hJ : IsSymmetricTensor J) :
    metricKineticCoefficient eta (planeJet p (pureGauge p v)) (planeJet (-p) J) = 0 := by
  rw [metricKineticCoefficient, metricDensity_eta]
  change 1 * kineticCoefficient (matrixInverse eta) _ _ = 0
  rw [matrixInverse_eta, kinetic_eta_plane_pureGauge p v J hJ, mul_zero]

end Burnett.Analysis.TransportWardSymbol
