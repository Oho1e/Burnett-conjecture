import Burnett.Analysis.TransportWard.Weyl.ScaledSymbolA01
import Burnett.Analysis.PrincipalEnergy.Localization.GlobalOrderOneSmoothAction
import Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

/-! Exact commutation of the actual left Fourier action with the two
spatial derivatives of a frozen Euler principal coefficient. -/

set_option autoImplicit false
set_option maxHeartbeats 6500000
set_option maxRecDepth 4500

noncomputable section

namespace Burnett.V03

open Function MeasureTheory Filter Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ContDiff FourierTransform RealInnerProductSpace

local notation "D" => frozenSchwartzCoordinatePartial

open private firstOrderAction_input_coordinateDerivative norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

private theorem physicalCoordinatePartial_add (i : Fin 4) (f g : E → ℂ) (x : E)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    physicalCoordinatePartial i (fun y => f y + g y) x =
      physicalCoordinatePartial i f x + physicalCoordinatePartial i g x := by
  simp only [physicalCoordinatePartial, fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]

theorem physicalCoordinatePartial_leftAction {a : E → E → ℂ} (h : ScaledJointOrderOne a)
    (i : Fin 4) (u : SchwartzMap E ℂ) (x : E) :
    physicalCoordinatePartial i (firstOrderAction a u) x =
      firstOrderAction a (D i u) x + firstOrderAction (baseDirectionSymbol a (coordinateDirection i)) u x := by
  let e := coordinateDirection i
  have hu := (firstOrderAction_contDiff_of_pureBaseOrder h.smooth h.pureBase u).differentiable (by simp) x
  have hl : HasDerivAt (fun t : ℝ => x + t • e) e 0 := by
    simpa only [id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add x
  have hDeriv : HasFDerivAt (firstOrderAction a u) (fderiv ℝ (firstOrderAction a u) x)
      ((fun t : ℝ => x + t • e) 0) := by
    simpa only [zero_smul, add_zero] using hu.hasFDerivAt
  have hd := hDeriv.comp_hasDerivAt (0 : ℝ) hl
  have hc := firstOrderAction_direction_commutator_of_jointSmooth h.firstBaseFrequency h.smooth u x e
  have heq : deriv (fun t : ℝ => firstOrderAction a u (x + t • e)) 0 =
      (fderiv ℝ (firstOrderAction a u) x) e := hd.deriv
  rw [heq] at hc
  exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)

theorem physicalCoordinatePartial_second_commutator {a : E → E → ℂ} (h : ScaledJointOrderOne a)
    (i j : Fin 4) (u : SchwartzMap E ℂ) (x : E) :
    physicalCoordinatePartial i (physicalCoordinatePartial j (firstOrderAction a u)) x -
      firstOrderAction a (D i (D j u)) x =
      firstOrderAction (baseDirectionSymbol a (coordinateDirection i)) (D j u) x +
      firstOrderAction (baseDirectionSymbol a (coordinateDirection j)) (D i u) x +
      firstOrderAction
        (baseDirectionSymbol (baseDirectionSymbol a (coordinateDirection j)) (coordinateDirection i)) u x := by
  let aj := baseDirectionSymbol a (coordinateDirection j)
  have hj := h.baseDirection (coordinateDirection j)
  have hDj : physicalCoordinatePartial j (firstOrderAction a u) =
      fun y => firstOrderAction a (D j u) y + firstOrderAction aj u y :=
    funext (physicalCoordinatePartial_leftAction h j u)
  have h1 := (firstOrderAction_contDiff_of_pureBaseOrder h.smooth h.pureBase (D j u)).differentiable (by simp) x
  have h2 := (firstOrderAction_contDiff_of_pureBaseOrder hj.smooth hj.pureBase u).differentiable (by simp) x
  rw [hDj, physicalCoordinatePartial_add i _ _ x h1 h2,
    physicalCoordinatePartial_leftAction h i (D j u) x,
    physicalCoordinatePartial_leftAction hj i u x]
  ring

/-- Exact scalar symbol of `i[-∂i∂j,Op_L(a)]` in the actual Fourier
frequency. Only the first two terms contribute at order two. -/
def frozenSecondCommutatorSymbol (a : E → E → ℂ) (i j : Fin 4) (x ξ : E) : ℂ :=
  (physicalRadianCovector ξ j : ℂ) * baseDirectionSymbol a (coordinateDirection i) x ξ +
    (physicalRadianCovector ξ i : ℂ) * baseDirectionSymbol a (coordinateDirection j) x ξ +
    (-Complex.I) * baseDirectionSymbol (baseDirectionSymbol a (coordinateDirection j)) (coordinateDirection i) x ξ

theorem frozenSecondCommutator_eq_leftAction {a : E → E → ℂ} (h : ScaledJointOrderOne a)
    (i j : Fin 4) (u : SchwartzMap E ℂ) (x : E) :
    (-Complex.I) * (physicalCoordinatePartial i (physicalCoordinatePartial j (firstOrderAction a u)) x -
      firstOrderAction a (D i (D j u)) x) = firstOrderAction (frozenSecondCommutatorSymbol a i j) u x := by
  let ai := baseDirectionSymbol a (coordinateDirection i)
  let aj := baseDirectionSymbol a (coordinateDirection j)
  let aij := baseDirectionSymbol aj (coordinateDirection i)
  let U (y ξ : E) := (physicalRadianCovector ξ j : ℂ) * ai y ξ
  let V (y ξ : E) := (physicalRadianCovector ξ i : ℂ) * aj y ξ
  let W (y ξ : E) := (-Complex.I) * aij y ξ
  have hi := h.baseDirection (coordinateDirection i)
  have hj := h.baseDirection (coordinateDirection j)
  have hij := hj.baseDirection (coordinateDirection i)
  have hProduct {b : E → E → ℂ} (hb : ScaledJointOrderOne b) (k : Fin 4) :
      Integrable (leftActionIntegrand (fun y ξ => (physicalRadianCovector ξ k : ℂ) * b y ξ) u x) volume := by
    have hκ : Continuous (fun ξ : E => (physicalRadianCovector ξ k : ℂ)) :=
      Complex.continuous_ofReal.comp ((EuclideanSpace.proj k).continuous.comp
        ((continuous_const : Continuous (fun _ : E => tau)).smul continuous_id))
    obtain ⟨C,C0,hC⟩ := hb.pureBase 0
    refine leftActionIntegrand_integrable_of_growth u x (hκ.mul (hb.firstBaseFrequency.frequency.smooth x).continuous)
      2 (M := tau*C) (fun ξ => ?_)
    have hb₀ : ‖b x ξ‖ ≤ C * (1+‖ξ‖) := by simpa only [norm_iteratedFDeriv_zero] using hC x ξ
    have hκ₀ := norm_physicalRadianCovector_le k ξ
    rw [norm_mul, Complex.norm_real]
    exact (mul_le_mul hκ₀ hb₀ (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hU : Integrable (leftActionIntegrand U u x) volume := hProduct hi j
  have hV : Integrable (leftActionIntegrand V u x) volume := hProduct hj i
  have hW₀ : Integrable (leftActionIntegrand aij u x) volume := by
    obtain ⟨C,_,hC⟩ := hij.pureBase 0
    exact leftActionIntegrand_integrable_of_growth u x (hij.firstBaseFrequency.frequency.smooth x).continuous
      1 (fun ξ => by simpa only [norm_iteratedFDeriv_zero,pow_one] using hC x ξ)
  have hW : Integrable (leftActionIntegrand W u x) volume := (hW₀.const_mul (-Complex.I)).congr
    (Eventually.of_forall fun ξ => by simp only [leftActionIntegrand,W]; ring)
  have hUV : Integrable (leftActionIntegrand (fun y ξ => U y ξ + V y ξ) u x) volume :=
    (hU.add hV).congr (Eventually.of_forall fun ξ => by
      change leftActionIntegrand U u x ξ + leftActionIntegrand V u x ξ = _
      simp only [leftActionIntegrand]
      ring)
  rw [physicalCoordinatePartial_second_commutator h i j u x,
    firstOrderAction_input_coordinateDerivative _ j u x, firstOrderAction_input_coordinateDerivative _ i u x]
  change (-Complex.I) * (Complex.I * firstOrderAction U u x +
    Complex.I * firstOrderAction V u x + firstOrderAction aij u x) =
      firstOrderAction (fun y ξ => (U y ξ + V y ξ) + W y ξ) u x
  rw [firstOrderAction_symbol_add u x hUV hW, firstOrderAction_symbol_add u x hU hV]
  change _ = firstOrderAction U u x + firstOrderAction V u x +
    firstOrderAction (fun y ξ => (-Complex.I) * aij y ξ) u x
  rw [firstOrderAction_symbol_scale]
  linear_combination -(firstOrderAction U u x + firstOrderAction V u x) * Complex.I_mul_I

end Burnett.V03
