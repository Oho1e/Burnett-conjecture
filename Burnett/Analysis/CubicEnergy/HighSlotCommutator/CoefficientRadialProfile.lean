import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientWindowTelescoping
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

set_option autoImplicit false
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Metric Set
open scoped ContDiff

private def coefficientRealRadialBump (a b : ℝ) (ha : 0<a) (hab : a<b) : ContDiffBump (0 : ℝ) :=
  ⟨a^2,b^2,pow_pos ha _,by nlinarith only [mul_pos (sub_pos.mpr hab) (add_pos ha (ha.trans hab))]⟩

/-- A real radial Schwartz low-pass in any fixed pair of positive nested
balls. Its support and plateau have the stated closed inequalities. -/
theorem exists_coefficientRadialProfile (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∃ χ : SchwartzMap E ℂ,
      HasCompactSupport (χ : E → ℂ) ∧
      (∀ x : E, ‖x‖≤a → χ x=1) ∧
      (∀ x : E, b≤‖x‖ → χ x=0) ∧
      ∀ x y : E, ‖x‖=‖y‖ → χ x=χ y := by
  let β := coefficientRealRadialBump a b ha hab
  let F := fun x : E => (β (‖x‖^2) : ℂ)
  have smooth : ContDiff ℝ ∞ F := Complex.ofRealCLM.contDiff.comp (β.contDiff.comp (contDiff_norm_sq ℝ))
  have oneAt (x : E) (hx : ‖x‖≤a) : F x=1 := by
    have h : ‖x‖^2 ∈ closedBall (0:ℝ) β.rIn := by
      rw [mem_closedBall,dist_zero_right,Real.norm_of_nonneg (sq_nonneg _)]
      change ‖x‖^2 ≤ a^2
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    simp only [F,β.one_of_mem_closedBall h,Complex.ofReal_one]
  have zeroAt (x : E) (hx : b≤‖x‖) : F x=0 := by
    have h : β.rOut ≤ dist (‖x‖^2) 0 := by
      rw [dist_zero_right,Real.norm_of_nonneg (sq_nonneg _)]
      change b^2 ≤ ‖x‖^2
      exact pow_le_pow_left₀ (ha.le.trans hab.le) hx 2
    simp only [F,β.zero_of_le_dist h,Complex.ofReal_zero]
  have hc : HasCompactSupport F := by
    refine (isCompact_closedBall (0:E) b).of_isClosed_subset isClosed_closure (closure_minimal ?_ isClosed_closedBall)
    intro x hx
    rw [mem_closedBall,dist_zero_right]
    exact (lt_of_not_ge (fun h => hx (zeroAt x h))).le
  exact ⟨hc.toSchwartzMap smooth,hc,oneAt,zeroAt,fun x y h => by change F x=F y; simp only [F,h]⟩

/-- A particular common low-pass produces a strict standard annulus and is
identically one at the limiting zero frequency. -/
theorem exists_coefficientDyadicProfile :
    ∃ χ : SchwartzMap E ℂ, HasCompactSupport (χ : E → ℂ) ∧ χ 0=1 ∧
      (∀ x : E, (7/4 : ℝ)≤‖x‖ → χ x=0) ∧
      HasCompactSupport (coefficientDyadicBandpass χ : E → ℂ) ∧
      ∀ x : E, coefficientDyadicBandpass χ x ≠ 0 → 1/2<‖x‖ ∧ ‖x‖<2 := by
  obtain ⟨χ,hc,h₁,h₀,_⟩ := exists_coefficientRadialProfile (5/4) (7/4) (by norm_num) (by norm_num)
  exact ⟨χ,hc,h₁ 0 (by norm_num),h₀,coefficientDyadicBandpass_compact χ hc,
    coefficientDyadicBandpass_annulus χ (by norm_num) (by norm_num) h₁ h₀⟩

end Burnett.A06
