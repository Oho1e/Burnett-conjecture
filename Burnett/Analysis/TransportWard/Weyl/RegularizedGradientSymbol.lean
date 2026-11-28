import Burnett.Analysis.TransportWard.Weyl.BaseDerivativeBounds
import Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights

set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 2100

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Filter MeasureTheory Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff BigOperators

local notation "D" => frozenSchwartzCoordinatePartial
local notation "W" => radianFrequencyWeight

/-- Squared length in the same physical radian frequency as the Weyl commutator. -/
def squaredRadianLength (ξ : E) : ℝ :=
  ∑ j : Fin 4, (physicalRadianCovector ξ j)^2

theorem squaredRadianLength_eq (ξ : E) : squaredRadianLength ξ = (tau * ‖ξ‖)^2 := by
  have hτ := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).le
  have hN : squaredRadianLength ξ = ‖tau • ξ‖^2 := by
    rw [EuclideanSpace.norm_sq_eq]
    simp only [squaredRadianLength, physicalRadianCovector, Real.norm_eq_abs, sq_abs]
  rw [hN,norm_smul,Real.norm_of_nonneg hτ]

private theorem squaredRadianLength_smooth : ContDiff ℝ ∞ squaredRadianLength :=
  ContDiff.sum (fun j _ =>
    ((ContinuousLinearMap.proj j : (Fin 4 → ℝ) →L[ℝ] ℝ).contDiff.comp
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).contDiff.comp
        (contDiff_const.smul contDiff_id : ContDiff ℝ ∞ (fun ξ : E => tau • ξ)))).pow 2)

/-- One fixed inhomogeneous inverse. The extra one removes the low-frequency
singularity and gives a genuine order-zero residual in the gradient transfer. -/
def regularizedGradientSymbol (p : E → E → ℂ) (x ξ : E) : ℂ :=
  ((1 + squaredRadianLength ξ : ℝ) : ℂ)⁻¹ * p x ξ

private theorem one_add_squaredRadianLength_pos (ξ : E) : 0 < 1 + squaredRadianLength ξ := by
  rw [squaredRadianLength_eq]
  positivity

theorem regularizedGradientSymbol_smooth {p : E → E → ℂ} (hs : ContDiff ℝ ∞ (uncurry p)) :
    ContDiff ℝ ∞ (uncurry (regularizedGradientSymbol p)) := by
  have hD : ContDiff ℝ ∞ (fun ξ : E => (1 + squaredRadianLength ξ : ℝ) : E → ℝ) :=
    contDiff_const.add squaredRadianLength_smooth
  have hInv := hD.inv (fun ξ => (one_add_squaredRadianLength_pos ξ).ne')
  have hC : ContDiff ℝ ∞ (fun ξ : E => ((1 + squaredRadianLength ξ : ℝ) : ℂ)⁻¹) := by
    have hJ : ContDiff ℝ ∞ (fun ξ : E => (((1 + squaredRadianLength ξ)⁻¹ : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp hInv
    simpa only [Complex.ofReal_inv] using hJ
  exact (hC.comp contDiff_snd).mul hs

theorem regularizedGradientSymbol_order_zero {p : E → E → ℂ}
    (hp : BaseDerivativeBounds p (fun ξ => (W ξ)^2)) :
    BaseDerivativeBounds (regularizedGradientSymbol p) (fun _ => 1) := by
  let m (ξ : E) := ((1 + squaredRadianLength ξ : ℝ) : ℂ)⁻¹
  have hW (ξ : E) : 0 < (W ξ)^2 := by
    change 0 < (1 + ‖ξ‖)^2
    positivity
  have hm (ξ : E) : ‖m ξ‖ ≤ 2 * ((W ξ)^2)⁻¹ := by
    have hτ : 1 ≤ tau := by
      change 1 ≤ 2 * Real.pi
      linarith only [Real.two_le_pi]
    rw [show ‖m ξ‖ = (1 + squaredRadianLength ξ)⁻¹ by
      rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg (one_add_squaredRadianLength_pos ξ).le]]
    rw [← one_div (1 + squaredRadianLength ξ), ← div_eq_mul_inv]
    apply (div_le_div_iff₀ (one_add_squaredRadianLength_pos ξ) (hW ξ)).mpr
    rw [squaredRadianLength_eq]
    change 1 * (1 + ‖ξ‖)^2 ≤ 2 * (1 + (tau * ‖ξ‖)^2)
    have hxi : ‖ξ‖ ≤ tau * ‖ξ‖ :=
      le_mul_of_one_le_left (norm_nonneg _) hτ
    have hxi₂ := pow_le_pow_left₀ (norm_nonneg ξ) hxi 2
    nlinarith only [sq_nonneg (‖ξ‖ - 1), hxi₂]
  have hM := BaseDerivativeBounds.frequency_multiplier m (fun ξ => ((W ξ)^2)⁻¹) 2
    (by norm_num) (fun ξ => inv_nonneg.mpr (hW ξ).le) hm
  exact (hM.mul hp (fun ξ => inv_nonneg.mpr (hW ξ).le)).weight_congr
    (fun ξ => inv_mul_cancel₀ (hW ξ).ne')

private theorem regularizedGradientSymbol_add_radian (p : E → E → ℂ) (x ξ : E) :
    p x ξ = regularizedGradientSymbol p x ξ +
      ∑ j : Fin 4, (physicalRadianCovector ξ j : ℂ)^2 * regularizedGradientSymbol p x ξ := by
  rw [← Finset.sum_mul, ← one_add_mul]
  change p x ξ = (1 + ∑ j : Fin 4, (physicalRadianCovector ξ j : ℂ)^2) *
    (((1 + squaredRadianLength ξ : ℝ) : ℂ)⁻¹ * p x ξ)
  have hCast : ((1 + squaredRadianLength ξ : ℝ) : ℂ) =
      1 + ∑ j : Fin 4, (physicalRadianCovector ξ j : ℂ)^2 := by
    dsimp only [squaredRadianLength]
    push_cast
    rfl
  have hD : ((1 + squaredRadianLength ξ : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (one_add_squaredRadianLength_pos ξ).ne'
  rw [← hCast, ← mul_assoc, mul_inv_cancel₀ hD, one_mul]

private theorem firstOrderAction_positive_radian_square (q : E → E → ℂ)
    (j : Fin 4) (u : SchwartzMap E ℂ) (x : E) :
    firstOrderAction (fun y ξ => (physicalRadianCovector ξ j : ℂ)^2 * q y ξ) u x =
      -firstOrderAction q (D j (D j u)) x := by
  rw [firstOrderAction_input_secondCoordinateDerivative, ← neg_one_mul, ← firstOrderAction_symbol_scale]
  apply congrArg (fun a => firstOrderAction a u x)
  funext y ξ
  ring

open private norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

private def radianSquaredSymbol (q : E → E → ℂ) (j : Fin 4) (x ξ : E) : ℂ :=
  (physicalRadianCovector ξ j : ℂ)^2 * q x ξ

private theorem leftActionIntegrand_radianSquared_integrable {q : E → E → ℂ}
    (u : SchwartzMap E ℂ) (x : E) (hCont : Continuous (q x))
    (C : ℝ) (hQ : ∀ ξ, ‖q x ξ‖ ≤ C) (j : Fin 4) :
    Integrable (leftActionIntegrand (radianSquaredSymbol q j) u x) volume := by
  have hContS : Continuous (radianSquaredSymbol q j x) :=
    ((physicalRadianCovector_complex_smooth j).continuous.pow 2).mul hCont
  refine leftActionIntegrand_integrable_of_growth u x hContS 2 (M := tau^2 * C) (fun ξ => ?_)
  rw [show ‖radianSquaredSymbol q j x ξ‖ = ‖physicalRadianCovector ξ j‖^2 * ‖q x ξ‖ by
    simp only [radianSquaredSymbol,norm_mul,norm_pow,Complex.norm_real]]
  refine (mul_le_mul
    (pow_le_pow_left₀ (norm_nonneg _) (norm_physicalRadianCovector_le j ξ) 2)
    (hQ ξ) (norm_nonneg _) (sq_nonneg _)).trans_eq ?_
  change (tau * W ξ)^2 * C = (tau^2*C) * (W ξ)^2
  generalize W ξ = w
  ring

private theorem firstOrderAction_of_radianSquaredPartition {p q : E → E → ℂ}
    (u : SchwartzMap E ℂ) (x : E)
    (hCont : Continuous (q x)) (C : ℝ) (hQ : ∀ ξ, ‖q x ξ‖ ≤ C)
    (hEq : ∀ ξ, p x ξ = q x ξ + ∑ j, radianSquaredSymbol q j x ξ) :
    firstOrderAction p u x = firstOrderAction q u x -
      ∑ j : Fin 4, firstOrderAction q (D j (D j u)) x := by
  let S := radianSquaredSymbol q
  have hIq : Integrable (leftActionIntegrand q u x) volume := by
    refine leftActionIntegrand_integrable_of_growth u x hCont 0 (M := C) (fun ξ => ?_)
    simpa only [pow_zero,mul_one] using hQ ξ
  have hIs (j : Fin 4) : Integrable (leftActionIntegrand (S j) u x) volume :=
    leftActionIntegrand_radianSquared_integrable u x hCont C hQ j
  have hSplit (ξ : E) : leftActionIntegrand p u x ξ =
      leftActionIntegrand q u x ξ + ∑ j, leftActionIntegrand (S j) u x ξ := by
    simp only [leftActionIntegrand,hEq ξ,S,add_mul,mul_add,Finset.sum_mul,Finset.mul_sum]
  have hSumInt : Integrable (fun ξ => ∑ j, leftActionIntegrand (S j) u x ξ) volume :=
    integrable_finset_sum _ (fun j _ => hIs j)
  simp only [firstOrderAction_eq_leftActionIntegrand p u x,hSplit]
  rw [integral_add hIq hSumInt, integral_finset_sum _ (fun j _ => hIs j),
    ← firstOrderAction_eq_leftActionIntegrand]
  have hSum : (∑ j : Fin 4, ∫ ξ, leftActionIntegrand (S j) u x ξ) =
      -∑ j : Fin 4, firstOrderAction q (D j (D j u)) x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => (firstOrderAction_eq_leftActionIntegrand (S j) u x).symm.trans
      (firstOrderAction_positive_radian_square q j u x))
  rw [hSum,sub_eq_add_neg]

/-- The exact order-two action equals the sum of four actual right
second-derivative actions of the bounded symbol and its order-zero term. -/
theorem firstOrderAction_regularizedGradientSymbol {p : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry p)) (hp : BaseDerivativeBounds p (fun ξ => (W ξ)^2))
    (u : SchwartzMap E ℂ) (x : E) :
    let q := regularizedGradientSymbol p
    firstOrderAction p u x = firstOrderAction q u x -
      ∑ j : Fin 4, firstOrderAction q (D j (D j u)) x := by
  intro q
  have hqs : ContDiff ℝ ∞ (uncurry q) := regularizedGradientSymbol_smooth hs
  obtain ⟨C,_,hB⟩ := (regularizedGradientSymbol_order_zero hp).bound 0
  have hQ (ξ : E) : ‖q x ξ‖ ≤ C := by
    simpa only [norm_iteratedFDeriv_zero,mul_one] using hB x ξ
  have hCont : Continuous (q x) := by
    change Continuous (uncurry q ∘ fun ξ : E => (x,ξ))
    exact hqs.continuous.comp (continuous_const.prodMk continuous_id)
  exact firstOrderAction_of_radianSquaredPartition u x hCont C hQ
    (regularizedGradientSymbol_add_radian p x)

end Burnett.V03
