import Burnett.Analysis.TransportWard.Weyl.CompactBaseZeroDerivative
import Burnett.Analysis.TransportWard.Weyl.RegularizedGradientSymbol
import Burnett.Analysis.Microlocal.Overlap.CompactClassicalQuantization
import Burnett.Analysis.PrincipalEnergy.Energy.SchwartzLeibniz
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights

set_option autoImplicit false
set_option maxHeartbeats 2700000
set_option maxRecDepth 2200

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Filter Set MeasureTheory Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy
open Burnett.Analysis.CarlesonEmbedding (baseDirectionSymbol_joint_smooth firstOrderAction_contDiff_of_pureBaseOrder)
open Burnett.Microlocal.Overlap (classicalLeftPairing exists_bounded_compactBaseZero_leftAction)
open scoped ContDiff Topology ComplexConjugate InnerProductSpace BigOperators

local notation "D" => frozenSchwartzCoordinatePartial
local notation "W" => radianFrequencyWeight

open private classicalLeftPairing_integrable from Burnett.Analysis.Microlocal.Overlap.ActualClassicalFullSymbol

theorem BaseDerivativeBounds.baseDirection {q : E → E → ℂ} {w : E → ℝ}
    (hq : BaseDerivativeBounds q w) (e : E) :
    BaseDerivativeBounds (baseDirectionSymbol q e) w := by
  have hs (ξ : E) : ContDiff ℝ ∞ (fderiv ℝ (fun y => q y ξ)) :=
    (hq.smooth ξ).fderiv_right (by simp)
  refine ⟨fun ξ => (hs ξ).clm_apply contDiff_const, fun n => ?_⟩
  obtain ⟨C,hC,hB⟩ := hq.bound (n+1)
  refine ⟨‖e‖*C,mul_nonneg (norm_nonneg _) hC,fun x ξ => ?_⟩
  have h1 : ‖iteratedFDeriv ℝ n (fun y => fderiv ℝ (fun z => q z ξ) y e) x‖ ≤
      ‖e‖ * ‖iteratedFDeriv ℝ n (fderiv ℝ (fun z => q z ξ)) x‖ :=
    norm_iteratedFDeriv_clm_apply_const (hs ξ).contDiffAt (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
  rw [norm_iteratedFDeriv_fderiv] at h1
  exact h1.trans ((mul_le_mul_of_nonneg_left (hB x ξ) (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm)

private theorem compactBaseZero_action_hasCompactSupport {q : E → E → ℂ} {K : Set E}
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, q x ξ = 0) (u : SchwartzMap E ℂ) :
    HasCompactSupport (firstOrderAction q u) := by
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hK.isClosed
  intro x hx
  by_contra hxK
  exact hx (by
    rw [firstOrderAction_eq_leftActionIntegrand]
    simp only [leftActionIntegrand,hZero x hxK,zero_mul,mul_zero,integral_zero])

private theorem firstOrderAction_orderZero_smooth {q : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry q)) (hq : BaseDerivativeBounds q (fun _ => 1)) (u : SchwartzMap E ℂ) :
    ContDiff ℝ ∞ (firstOrderAction q u) := by
  apply firstOrderAction_contDiff_of_pureBaseOrder hs _ u
  intro n
  obtain ⟨C,hC,h⟩ := hq.bound n
  refine ⟨C,hC,fun x ξ => (h x ξ).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (norm_nonneg _)) hC

private theorem classicalLeftPairing_integrable_of_orderZero {q : E → E → ℂ}
    (hs : ContDiff ℝ ∞ (uncurry q)) (hq : BaseDerivativeBounds q (fun _ => 1))
    (v u : SchwartzMap E ℂ) :
    Integrable (fun x => conj (v x) * firstOrderAction q u x) volume := by
  obtain ⟨C,_,hC⟩ := hq.bound 0
  exact classicalLeftPairing_integrable hs.continuous.measurable
    (fun x ξ => by simpa only [norm_iteratedFDeriv_zero,mul_one] using hC x ξ) v u

private theorem quantumCoordinatePartial_integral {q : E → E → ℂ} {K : Set E}
    (hs : ContDiff ℝ ∞ (uncurry q)) (hq : BaseDerivativeBounds q (fun _ => 1))
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, q x ξ = 0)
    (u v : SchwartzMap E ℂ) (j : Fin 4) :
    (∫ x, conj (v x) * physicalCoordinatePartial j (firstOrderAction q u) x) =
      - classicalLeftPairing q (D j v) u := by
  let F := (compactBaseZero_action_hasCompactSupport hK hZero u).toSchwartzMap
    (firstOrderAction_orderZero_smooth hs hq u)
  have hSk := schwartz_derivative_isSkew (coordinateDirection j)
    (schwartzTestEquiv v) (schwartzTestEquiv F)
  simp only [schwartzDerivative, transportSchwartzOp_on_equiv, schwartzTestEquiv_inner,
    ContinuousLinearMap.coe_coe] at hSk
  have hp : classicalLeftPairing q (D j v) u =
      -(∫ x, conj (v x) * physicalCoordinatePartial j (firstOrderAction q u) x) := by
    simpa only [RCLike.inner_apply',classicalLeftPairing,F,frozenSchwartzCoordinatePartial,
      physicalCoordinatePartial,SchwartzMap.pderivCLM_apply] using hSk
  rw [hp, neg_neg]

private theorem negative_second_action_pairing {q : E → E → ℂ} {K : Set E}
    (hs : ContDiff ℝ ∞ (uncurry q)) (hq : BaseDerivativeBounds q (fun _ => 1))
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, q x ξ = 0)
    (u v : SchwartzMap E ℂ) (j : Fin 4) :
    - classicalLeftPairing q v (D j (D j u)) =
      classicalLeftPairing q (D j v) (D j u) +
        classicalLeftPairing (baseDirectionSymbol q (coordinateDirection j)) v (D j u) := by
  let Q := baseDirectionSymbol q (coordinateDirection j)
  have hI₁ := classicalLeftPairing_integrable_of_orderZero
    (baseDirectionSymbol_joint_smooth hs (coordinateDirection j)) (hq.baseDirection _) v (D j u)
  have hI₂ := classicalLeftPairing_integrable_of_orderZero hs hq v (D j (D j u))
  have hD : (fun x => conj (v x) * physicalCoordinatePartial j (firstOrderAction q (D j u)) x) =
      fun x => conj (v x) * firstOrderAction Q (D j u) x + conj (v x) * firstOrderAction q (D j (D j u)) x := by
    funext x
    rw [physicalCoordinatePartial_leftAction_of_orderZero hs hq,mul_add]
  have hIBP := quantumCoordinatePartial_integral hs hq hK hZero (D j u) v j
  rw [hD,integral_add hI₁ hI₂] at hIBP
  change classicalLeftPairing Q v (D j u) + classicalLeftPairing q v (D j (D j u)) =
    - classicalLeftPairing q (D j v) (D j u) at hIBP
  linear_combination -hIBP

/-- The complete second-order principal pairing becomes a sum of four
actual zero-order tests between gradients and only lower-order terms. -/
theorem classicalLeftPairing_regularizedGradientSymbol {p : E → E → ℂ} {K : Set E}
    (hs : ContDiff ℝ ∞ (uncurry p)) (hp : BaseDerivativeBounds p (fun ξ => (W ξ)^2))
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, p x ξ = 0) (u v : SchwartzMap E ℂ) :
    let q := regularizedGradientSymbol p
    classicalLeftPairing p v u = classicalLeftPairing q v u +
      ∑ j : Fin 4, (classicalLeftPairing q (D j v) (D j u) +
        classicalLeftPairing (baseDirectionSymbol q (coordinateDirection j)) v (D j u)) := by
  intro q
  have hqS := regularizedGradientSymbol_smooth hs
  have hqB := regularizedGradientSymbol_order_zero hp
  have hqZero (x : E) (hx : x ∉ K) (ξ : E) : q x ξ = 0 := by
    simp only [q,regularizedGradientSymbol,hZero x hx,mul_zero]
  have hi₀ := classicalLeftPairing_integrable_of_orderZero hqS hqB v u
  have hi₁ (j : Fin 4) := classicalLeftPairing_integrable_of_orderZero hqS hqB v (D j (D j u))
  have he : classicalLeftPairing p v u = classicalLeftPairing q v u -
       ∑ j : Fin 4, classicalLeftPairing q v (D j (D j u)) := by
    unfold classicalLeftPairing
    have hAct (x : E) := firstOrderAction_regularizedGradientSymbol hs hp u x
    have hf : (fun x => conj (v x) * firstOrderAction p u x) =
        fun x => conj (v x) * firstOrderAction q u x -
          ∑ j : Fin 4, conj (v x) * firstOrderAction q (D j (D j u)) x := by
      funext x
      rw [hAct,mul_sub,Finset.mul_sum]
    rw [hf,integral_sub hi₀ (integrable_finset_sum _ (fun j _ => hi₁ j)),
      integral_finset_sum _ (fun j _ => hi₁ j)]
  rw [he,sub_eq_add_neg,← Finset.sum_neg_distrib]
  exact congrArg (fun z : ℂ => classicalLeftPairing q v u + z)
    (Finset.sum_congr rfl (fun j _ => negative_second_action_pairing hqS hqB hK hqZero u v j))

end Burnett.V03
