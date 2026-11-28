import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalCoordinateActionBounds
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalOrderOneSmoothAction
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichFrequency
import Burnett.Analysis.PrincipalEnergy.Quantization.CompactBaseFourier
import Burnett.Analysis.Microlocal.Overlap.BaseFourierAction

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 1900
namespace Burnett.V03

open Function MeasureTheory Filter Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.Microlocal.Overlap (baseFourierPhase baseFourierPhase_norm baseFourierPhase_continuous)
open scoped BigOperators ContDiff FourierTransform RealInnerProductSpace

-- V03FrozenScalarCommutator.lean SHA256 7f8a8311b357f9fbbc8fa04633a9f9bd325acd37f78dfafe1be6e1f9089340fa
/-- The same coordinate derivative on Schwartz inputs. -/
def frozenSchwartzCoordinatePartial (i : Fin 4) : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.pderivCLM ℂ (coordinateDirection i)

local notation "D" => frozenSchwartzCoordinatePartial

/-- A physical coordinate derivative of a smooth output function. -/
def physicalCoordinatePartial (i : Fin 4) (u : E → ℂ) (x : E) : ℂ :=
  fderiv ℝ u x (coordinateDirection i)

-- V03FrozenScalarCommutator.lean SHA256 7f8a8311b357f9fbbc8fa04633a9f9bd325acd37f78dfafe1be6e1f9089340fa
/-- The actual radian covector evaluated at a mathlib frequency. -/
def physicalRadianCovector (ξ : E) : Fin 4 → ℝ := fun j => (tau • ξ) j

private theorem norm_physicalRadianCovector_le (j : Fin 4) (ξ : E) :
    ‖physicalRadianCovector ξ j‖ ≤ tau * (1 + ‖ξ‖) := by
  have ht : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  calc
    _ ≤ ‖tau • ξ‖ := PiLp.norm_apply_le (tau • ξ) j
    _ = tau * ‖ξ‖ := by rw [norm_smul, Real.norm_of_nonneg ht]
    _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left zero_le_one) ht

/-- The full left integral is well defined on Schwartz inputs for every
polynomial symbol order, including the order-two symbols below. -/
def leftActionIntegrand (a : E → E → ℂ) (u : SchwartzMap E ℂ) (x ξ : E) : ℂ :=
  baseFourierPhase ξ x * a x ξ * (𝓕 (u : E → ℂ)) ξ

theorem firstOrderAction_eq_leftActionIntegrand (a : E → E → ℂ) (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction a u x = ∫ ξ, leftActionIntegrand a u x ξ := by
  simp only [firstOrderAction, Real.fourierIntegralInv_eq', leftActionIntegrand, baseFourierPhase,
    smul_eq_mul, mul_assoc]

theorem leftActionIntegrand_integrable_of_growth {a : E → E → ℂ} (u : SchwartzMap E ℂ) (x : E)
    (h : Continuous (a x)) (m : ℕ) {M : ℝ} (hM : ∀ ξ, ‖a x ξ‖ ≤ M * (1 + ‖ξ‖)^m) :
    Integrable (leftActionIntegrand a u x) (volume : Measure E) := by
  let F := SchwartzMap.fourierTransformCLM ℂ u
  have hPhase := baseFourierPhase_continuous.comp
    (continuous_id.prodMk (continuous_const : Continuous (fun _ : E => x)))
  have hCont : Continuous (leftActionIntegrand a u x) := (hPhase.mul h).mul F.continuous
  refine ((integrable_schwartz_weighted F m).const_mul M).mono' hCont.aestronglyMeasurable ?_
  filter_upwards with ξ
  simp only [leftActionIntegrand, norm_mul, baseFourierPhase_norm, one_mul]
  exact (mul_le_mul_of_nonneg_right (hM ξ) (norm_nonneg _)).trans_eq (by
    simp only [F, SchwartzMap.fourierTransformCLM_apply]
    ring)

theorem firstOrderAction_symbol_add {a b : E → E → ℂ} (u : SchwartzMap E ℂ) (x : E)
    (ha : Integrable (leftActionIntegrand a u x) volume) (hb : Integrable (leftActionIntegrand b u x) volume) :
    firstOrderAction (fun y ξ => a y ξ + b y ξ) u x = firstOrderAction a u x + firstOrderAction b u x := by
  simp only [firstOrderAction_eq_leftActionIntegrand, ← integral_add ha hb]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by simp only [leftActionIntegrand]; ring

theorem firstOrderAction_symbol_scale (a : E → E → ℂ) (z : ℂ) (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (fun y ξ => z * a y ξ) u x = z * firstOrderAction a u x := by
  simp only [firstOrderAction_eq_leftActionIntegrand, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by simp only [leftActionIntegrand]; ring

private theorem firstOrderAction_input_coordinateDerivative (a : E → E → ℂ) (j : Fin 4)
    (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction a (D j u) x =
      Complex.I * firstOrderAction (fun y ξ => (physicalRadianCovector ξ j : ℂ) * a y ξ) u x := by
  rw [← firstOrderAction_symbol_scale]
  simp only [firstOrderAction_eq_leftActionIntegrand]
  apply integral_congr_ae
  filter_upwards with ξ
  have hf : (𝓕 ((D j u : SchwartzMap E ℂ) : E → ℂ)) ξ =
      Complex.I * (physicalRadianCovector ξ j : ℂ) * (𝓕 (u : E → ℂ)) ξ := by
    rw [frozenSchwartzCoordinatePartial, Burnett.Analysis.HminusWeightedDual.fourier_pderiv,
      coordinateDirection, EuclideanSpace.inner_single_right]
    simp only [one_mul, conj_trivial, physicalRadianCovector, tau, PiLp.smul_apply, smul_eq_mul]
    push_cast
    ring
  simp only [leftActionIntegrand, hf]
  ring

-- V03RadianWeylDerivative.lean SHA256 d2cd20b1b1210c02e18f1f5f1c7a763720c4b3d1b7553530401e445a94e705ae
/-- The physical second derivative inserts the negative product of the
two radian coordinates into the exact Fourier action. -/
theorem firstOrderAction_input_secondCoordinateDerivative (a : E → E → ℂ)
    (i j : Fin 4) (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction a (frozenSchwartzCoordinatePartial i (frozenSchwartzCoordinatePartial j u)) x =
      firstOrderAction (fun y ξ => -((physicalRadianCovector ξ i : ℂ) *
        (physicalRadianCovector ξ j : ℂ)) * a y ξ) u x := by
  rw [firstOrderAction_input_coordinateDerivative _ i (frozenSchwartzCoordinatePartial j u) x,
    firstOrderAction_input_coordinateDerivative _ j u x, ← firstOrderAction_symbol_scale,
    ← firstOrderAction_symbol_scale]
  apply congrArg (fun b => firstOrderAction b u x)
  funext y ξ
  linear_combination
    ((physicalRadianCovector ξ i : ℂ) * (physicalRadianCovector ξ j : ℂ) * a y ξ) * Complex.I_mul_I

-- V03FrozenWeylOperatorRemainder.lean SHA256 65c164bf488ef5cc2b83952e6c98e9ae76915046509c792a565b32483d51202d
theorem physicalRadianCovector_complex_smooth (j : Fin 4) :
    ContDiff ℝ ∞ (fun ξ : E => (physicalRadianCovector ξ j : ℂ)) := by
  have hs : ContDiff ℝ ∞ (fun ξ : E => tau • ξ) := contDiff_const.smul contDiff_id
  have hj : ContDiff ℝ ∞ (fun ξ : E => ξ j) := (EuclideanSpace.proj j : E →L[ℝ] ℝ).contDiff
  exact Complex.ofRealCLM.contDiff.comp (hj.comp hs)

end Burnett.V03
