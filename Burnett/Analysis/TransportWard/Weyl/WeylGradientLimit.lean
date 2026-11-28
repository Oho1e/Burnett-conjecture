import Burnett.Analysis.TransportWard.Weyl.CompactBaseZeroDerivative
import Burnett.Analysis.TransportWard.Weyl.RegularizedGradientSymbol
import Burnett.Analysis.TransportWard.Weyl.WeylGradientPairing
import Burnett.Analysis.TransportWard.Weyl.HomogeneousGradientTest
import Burnett.Analysis.TransportWard.Weyl.RadianParameterWeights

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2000

noncomputable section

namespace Burnett.V03

open Burnett.A03 (RadianParameter radianFrequencyWeight radian_frequency_weight_pos)


open Function Filter Set MeasureTheory Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Analysis.SymmetricEnergy (coordinateDirection)
open Burnett.Analysis.CarlesonEmbedding (baseDirectionSymbol_joint_smooth)
open Burnett.Microlocal.Overlap (classicalLeftPairing exists_bounded_compactBaseZero_leftAction)
open scoped ContDiff Topology InnerProductSpace BigOperators

local notation "D" => frozenSchwartzCoordinatePartial

private theorem tendsto_classicalLeftPairing_zero_of_uniformL2 {p : E → E → ℂ} {K : Set E}
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, p x ξ = 0)
    (hs : ContDiff ℝ ∞ (uncurry p)) (hb : BaseDerivativeBounds p (fun _ => 1))
    (u v : ℕ → SchwartzMap E ℂ) (M : ℝ) (hU : ∀ n, ‖(u n).toLp 2 volume‖ ≤ M)
    (hV : Tendsto (fun n => ‖(v n).toLp 2 volume‖) atTop (𝓝 0)) :
    Tendsto (fun n => classicalLeftPairing p (v n) (u n)) atTop (𝓝 0) := by
  have hSupp (ξ : E) : tsupport (fun x => p x ξ) ⊆ K :=
    closure_minimal (fun x hx => by by_contra h; exact hx (hZero x h ξ)) hK.isClosed
  have hBounds (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ, ‖iteratedFDeriv ℝ n (fun y => p y ξ) x‖ ≤ C := by
    simpa only [mul_one] using hb.bound n
  obtain ⟨T,hT⟩ := exists_bounded_compactBaseZero_leftAction p K hK hSupp hs hBounds
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hLim : Tendsto (fun n => ‖(v n).toLp 2 volume‖ * (‖T‖ * M)) atTop (𝓝 0) := by
    simpa only [zero_mul] using hV.mul_const (‖T‖ * M)
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hLim
  rw [← hT (v n) (u n)]
  exact (norm_inner_le_norm (𝕜 := ℂ) _ _).trans (mul_le_mul_of_nonneg_left
    ((T.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hU n) (norm_nonneg T))) (norm_nonneg _))

/-- All extra terms from moving the actual left derivatives tend to zero
under the original bounded-H¹ and strong-L² regime. -/
theorem tendsto_classicalLeftPairing_sub_regularizedGradientPair_zero {p : E → E → ℂ} {K : Set E}
    (hs : ContDiff ℝ ∞ (uncurry p))
    (hp : BaseDerivativeBounds p (fun ξ => (1 + ‖ξ‖)^2))
    (hK : IsCompact K) (hZero : ∀ x ∉ K, ∀ ξ, p x ξ = 0)
    (u v : ℕ → SchwartzMap E ℂ) (M : ℝ)
    (hU : ∀ n, ‖(u n).toLp 2 volume‖ ≤ M)
    (hD : ∀ j : Fin 4, ∀ n, ‖(D j (u n)).toLp 2 volume‖ ≤ M)
    (hV : Tendsto (fun n => ‖(v n).toLp 2 volume‖) atTop (𝓝 0)) :
    let q := regularizedGradientSymbol p
    Tendsto (fun n => classicalLeftPairing p (v n) (u n) -
      ∑ j : Fin 4, classicalLeftPairing q (D j (v n)) (D j (u n))) atTop (𝓝 0) := by
  intro q
  have hqS := regularizedGradientSymbol_smooth hs
  have hqB := regularizedGradientSymbol_order_zero hp
  have hqZero (x : E) (hx : x ∉ K) (ξ : E) : q x ξ = 0 := by
    simp only [q,regularizedGradientSymbol,hZero x hx,mul_zero]
  have hL := tendsto_classicalLeftPairing_zero_of_uniformL2 hK hqZero hqS hqB u v M hU hV
  let R (j : Fin 4) := baseDirectionSymbol q (coordinateDirection j)
  let F (j : Fin 4) (n : ℕ) := classicalLeftPairing (R j) (v n) (D j (u n))
  have hF (j : Fin 4) : Tendsto (F j) atTop (𝓝 0) := by
    have hR (x : E) (hx : x ∉ K) (ξ : E) : R j x ξ = 0 := by
      have hNear : (fun y => q y ξ) =ᶠ[𝓝 x] fun _ => 0 := by
        filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
        exact hqZero y hy ξ
      simp only [R,baseDirectionSymbol,hNear.fderiv_eq,fderiv_const_apply,ContinuousLinearMap.zero_apply]
    exact tendsto_classicalLeftPairing_zero_of_uniformL2 hK hR
      (baseDirectionSymbol_joint_smooth hqS _) (hqB.baseDirection _)
      (fun n => D j (u n)) v M (hD j) hV
  have hSum : Tendsto (fun n => ∑ j, F j n) atTop (𝓝 0) := by
    simpa only [Finset.sum_const_zero] using tendsto_finset_sum Finset.univ (fun j _ => hF j)
  have hFinal : Tendsto (fun n => classicalLeftPairing q (v n) (u n) + ∑ j, F j n) atTop (𝓝 0) := by
    simpa only [add_zero] using hL.add hSum
  refine hFinal.congr (fun n => ?_)
  rw [classicalLeftPairing_regularizedGradientSymbol hs hp hK hZero,
    Finset.sum_add_distrib]
  abel

end Burnett.V03
