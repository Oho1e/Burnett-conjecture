import Burnett.Analysis.TransportWard.Weyl.FrozenScalarCommutator
import Burnett.Analysis.TransportWard.Weyl.WindowedWeylFullSymbol

/-! Lower symbol order for the terms dropped from the exact frozen Weyl
commutator on the same compact windows. -/

set_option autoImplicit false
set_option maxHeartbeats 7400000
set_option maxRecDepth 4800

noncomputable section

namespace Burnett.V03

open Function Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open scoped BigOperators ContDiff

open private baseDirectionSymbol_eq_joint from Burnett.Analysis.TransportWard.Weyl.ScaledSymbolA01
open private norm_physicalRadianCovector_le from Burnett.Analysis.TransportWard.Weyl.FourierCoordinateAction

private theorem bounded_baseDirection_of_scaled_order_zero {r : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry r))
    (h : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ p : RadianParameter,
        ‖radianScaledParameterJet (uncurry r) n p‖ ≤ C) (e : E) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖baseDirectionSymbol r e x ξ‖ ≤ C := by
  obtain ⟨C, hC, hb⟩ := h 1
  let v : RadianParameter := (e,0)
  refine ⟨C * ‖v‖, mul_nonneg hC (norm_nonneg v), fun x ξ => ?_⟩
  have hn := (radian_parameter_jet_norm_le_scaled (uncurry r) 1 (x,ξ)).trans (hb (x,ξ))
  rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] at hn
  rw [baseDirectionSymbol_eq_joint r hs e (x,ξ)]
  exact ((fderiv ℝ (uncurry r) (x,ξ)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hn (norm_nonneg v))

theorem frozenSecondCompactWeylSymbol_sub_leading_growth
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (hAmp : RadianOrdinaryDirectionalAmplitudeBounds (windowedWeylAmplitude θ β))
    (hPlateau : ∀ x ξ, β x ξ ≠ 0 → θ x = 1)
    (hβ : ScaledJointOrderOne (normalizedWeylSymbol β)) (i j : Fin 4) :
    let a := windowedWeylLeftSymbol θ β R h
    let b := normalizedWeylSymbol β
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖frozenSecondCommutatorSymbol a i j x ξ -
        ((physicalRadianCovector ξ j : ℂ) * baseDirectionSymbol b (coordinateDirection i) x ξ +
          (physicalRadianCovector ξ i : ℂ) * baseDirectionSymbol b (coordinateDirection j) x ξ)‖ ≤
        C * (1 + ‖ξ‖) := by
  intro a b
  let r (x ξ : E) := a x ξ - b x ξ
  have ha := windowedWeyl_leftSymbol_scaled_order_one θ β R h hAmp hPlateau hβ
  obtain ⟨hR, hBounds⟩ := windowedWeyl_leftSymbol_scaled_remainder θ β R h hAmp hPlateau
  obtain ⟨C, hC, hCi⟩ := bounded_baseDirection_of_scaled_order_zero hR hBounds (coordinateDirection i)
  obtain ⟨D, hD, hDj⟩ := bounded_baseDirection_of_scaled_order_zero hR hBounds (coordinateDirection j)
  have hSecond := (ha.baseDirection (coordinateDirection j)).baseDirection (coordinateDirection i)
  obtain ⟨L, hL, hLab⟩ := hSecond.pureBase 0
  have hτ : 0 ≤ tau := (mul_pos (by norm_num) Real.pi_pos).le
  refine ⟨tau*C + tau*D + L, by positivity, fun x ξ => ?_⟩
  have hBase (e : E) :
      baseDirectionSymbol a e x ξ = baseDirectionSymbol b e x ξ + baseDirectionSymbol r e x ξ := by
    have he : (fun y => a y ξ) = (fun y => b y ξ + r y ξ) := by
      funext y
      simp only [r]
      ring
    have hPair : ContDiff ℝ ∞ (fun y : E => (y,ξ)) := contDiff_id.prodMk contDiff_const
    have hbDiff : DifferentiableAt ℝ (fun y => b y ξ) x :=
      (hβ.smooth.comp hPair).differentiable (by simp) x
    have hrDiff : DifferentiableAt ℝ (fun y => r y ξ) x :=
      (hR.comp hPair).differentiable (by simp) x
    change (fderiv ℝ (fun y => a y ξ) x) e = (fderiv ℝ (fun y => b y ξ) x) e +
      (fderiv ℝ (fun y => r y ξ) x) e
    rw [he, fderiv_fun_add hbDiff hrDiff, ContinuousLinearMap.add_apply]
  let U := (physicalRadianCovector ξ j : ℂ) * baseDirectionSymbol r (coordinateDirection i) x ξ
  let V := (physicalRadianCovector ξ i : ℂ) * baseDirectionSymbol r (coordinateDirection j) x ξ
  let W := (-Complex.I) * baseDirectionSymbol (baseDirectionSymbol a (coordinateDirection j)) (coordinateDirection i) x ξ
  have heq :
      frozenSecondCommutatorSymbol a i j x ξ -
        ((physicalRadianCovector ξ j : ℂ) * baseDirectionSymbol b (coordinateDirection i) x ξ +
          (physicalRadianCovector ξ i : ℂ) * baseDirectionSymbol b (coordinateDirection j) x ξ) =
      U + V + W := by
    simp only [frozenSecondCommutatorSymbol, hBase, U, V, W]
    ring
  have hU : ‖U‖ ≤ tau*(1+‖ξ‖)*C := by
    simp only [U, norm_mul, Complex.norm_real]
    exact mul_le_mul (norm_physicalRadianCovector_le j ξ) (hCi x ξ) (norm_nonneg _) (by positivity)
  have hV : ‖V‖ ≤ tau*(1+‖ξ‖)*D := by
    simp only [V, norm_mul, Complex.norm_real]
    exact mul_le_mul (norm_physicalRadianCovector_le i ξ) (hDj x ξ) (norm_nonneg _) (by positivity)
  have hW : ‖W‖ ≤ L*(1+‖ξ‖) := by
    simp only [W, norm_mul, norm_neg, Complex.norm_I, one_mul]
    simpa only [norm_iteratedFDeriv_zero] using hLab x ξ
  rw [heq]
  calc
    _ ≤ ‖U‖ + ‖V‖ + ‖W‖ := (norm_add_le _ _).trans (add_le_add_right (norm_add_le _ _) _)
    _ ≤ _ := (add_le_add (add_le_add hU hV) hW).trans_eq (by ring)

end Burnett.V03
