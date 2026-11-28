import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhaseTransfer

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.C02

open Set Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight lowSlotWeight_nonzero_small)
open Burnett.RicciSymbol (Tensor2)
open scoped ContDiff

/-- The original first-low cutoff applied to the raw degree-three
Ward coefficient. The frequency axes use its zero extension. -/
def wardActualLowCut (ϑ : ℝ → ℝ) (κ : ℝ) (A : Joint → ℂ) (x : Joint) : ℂ := by
  classical
  exact if x.1 ≠ 0 ∧ x.2 ≠ 0 then
    (lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) : ℂ) * A x
  else 0

theorem wardActualLowCut_eq_sum_phases {ι : Type*} [Fintype ι] (ϑ : ℝ → ℝ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (A : Joint → ℂ) (F : ι → WardLowPoint → ℂ) (j : ι → Fin 3)
    (hMatch : ∀ x ∈ wardLowActive,
      A x = ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ) *
        ∑ i, F i (wardLowInput x) * (normalizedFrozenPhase m (wardPhaseCovector x (j i)) : ℂ)) :
    ∀ x, wardActualLowCut ϑ κ A x =
      ∑ i, wardLowRadialSymbol ϑ κ (F i) x * (normalizedFrozenPhase m (wardPhaseCovector x (j i)) : ℂ) := by
  classical
  intro x
  by_cases hx : x ∈ wardLowActive
  · rw [wardActualLowCut, if_pos ⟨hx.1,hx.2.1⟩, hMatch x hx]
    simp only [wardLowRadialSymbol, wardLowSlotSymbol, piecewise_eq_of_mem _ _ _ hx]
    rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · have hOff (i : ι) : wardLowRadialSymbol ϑ κ (F i) x = 0 := by
      simp only [wardLowRadialSymbol, wardLowSlotSymbol, piecewise_eq_of_notMem _ _ _ hx, Pi.zero_apply, zero_mul]
    simp only [hOff, zero_mul, Finset.sum_const_zero]
    rw [wardActualLowCut]
    split_ifs with h
    · have hL : lowSlotWeight ϑ κ x.1 x.2 (-(x.1+x.2)) = 0 := by
        by_contra hL
        have hb := lowSlotWeight_nonzero_small hCut hκ hSmall (add_neg_cancel (x.1+x.2)) h.2 hL
        have ht := (div_le_iff₀ (norm_pos_iff.mpr h.2)).mpr hb
        exact hx ⟨h.1,h.2,ht.trans_lt (by linarith only [hSmall])⟩
      simp only [hL, Complex.ofReal_zero, zero_mul]
    · rfl

theorem wardLowActive_radialProduct_ne_zero {x : Joint} (hx : x ∈ wardLowActive) :
    ((‖x.1‖ * ‖x.2‖ * ‖-(x.1+x.2)‖ : ℝ) : ℂ) ≠ 0 := by
  have hr : -(x.1+x.2) ≠ 0 := by
    intro h
    have he : x.1 = -x.2 := eq_neg_of_add_eq_zero_left (neg_eq_zero.mp h)
    have hb := hx.2.2
    rw [he, norm_neg, div_self (norm_ne_zero_iff.mpr hx.2.1)] at hb
    norm_num at hb
  exact Complex.ofReal_ne_zero.mpr
    (mul_ne_zero (mul_ne_zero (norm_ne_zero_iff.mpr hx.1) (norm_ne_zero_iff.mpr hx.2.1))
      (norm_ne_zero_iff.mpr hr))

end Burnett.C02
