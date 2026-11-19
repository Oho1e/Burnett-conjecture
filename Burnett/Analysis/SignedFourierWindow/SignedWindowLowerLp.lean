import Burnett.Analysis.SignedFourierWindow.SignedWindowWeak
import Burnett.Analysis.SignedFourierWindow.InterpolationMoment
import Burnett.Analysis.SignedFourierWindow.KernelLpExhaustion

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory
open scoped NNReal ENNReal

/-- Uniform strong bounds below exponent two for the exact finite, modulated,
signed annular convolutions, on the full Lᵖ space. -/
theorem signed_window_lower_Lp (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p : ℝ) (hp : 1<p) (hp2 : p<2) :
    ∃ V : ℝ≥0∞, V < ⊤ ∧ ∀ t : ℝ, 0<t → ∀ (q : Space) (I : Finset ℕ) (c : ℕ → ℂ),
      (∀ k, ‖c k‖ ≤ 1) → ∀ f : Space → ℂ, MemLp f (ENNReal.ofReal p) volume →
      let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
      eLpNorm (kernelApply K f) (ENNReal.ofReal p) volume ≤
        (V*(ENNReal.ofReal (1+‖q‖))^(1/p))*eLpNorm f (ENNReal.ofReal p) volume := by
  obtain ⟨W,wfin,weak⟩ := signed_window_weak_one a ha cut
  obtain ⟨_,_,est⟩ := signed_window_operator_estimates a ha cut
  let B := 2*SchwartzMap.seminorm ℝ 0 0 a
  let P := ENNReal.ofReal ((2:ℝ)^p*p)
  let X := W*ENNReal.ofReal (p-1)⁻¹
  let Y := (ENNReal.ofReal B)^2*ENNReal.ofReal (2-p)⁻¹
  let V := (P*(X+Y))^(1/p)
  have hp0 : 0<p := by linarith
  have ip : 0≤1/p := (one_div_pos.mpr hp0).le
  have Vfin : V<⊤ := ENNReal.rpow_lt_top_of_nonneg ip (by dsimp only [P,X,Y]; finiteness)
  refine ⟨V,Vfin,?_⟩
  intro t ht q I c hc f hf
  let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
  let J := ENNReal.ofReal (1+‖q‖)
  have jone : 1≤J := by simp [J]
  obtain ⟨hK,hi,h2,D,hD⟩ := finite_kernel_regular ((SchwartzMap.fourierTransformCLE ℂ).symm a) t ht q I c
  have w (h : Space → ℂ) (hh : Integrable h) (z : ℝ) (hz : 0<z) :
      ENNReal.ofReal z * volume {x | z < ‖kernelApply K h x‖} ≤ (W*J)*∫⁻ x, ‖h x‖ₑ := by
    have h0 := weak t ht q I c hc h hh (z.toNNReal) (Real.toNNReal_pos.mpr hz)
    change ENNReal.ofReal z * volume {x | ENNReal.ofReal z < ‖kernelApply K h x‖ₑ} ≤ _ at h0
    have sets : {x | ENNReal.ofReal z < ‖kernelApply K h x‖ₑ} = {x | z < ‖kernelApply K h x‖} := by
      ext x
      simp only [Set.mem_setOf_eq,← ofReal_norm_eq_enorm,ENNReal.ofReal_lt_ofReal_iff_of_nonneg hz.le]
    rwa [sets] at h0
  have hB : 0≤B := mul_nonneg (by norm_num) (apply_nonneg _ _)
  have strong := kernelApply_L2_extension K h2 B hB (est t ht q I c hc).2
  have coef : P*((W*J)*ENNReal.ofReal (p-1)⁻¹+Y) ≤ (P*(X+Y))*J := by
    calc
      _ ≤ P*((W*J)*ENNReal.ofReal (p-1)⁻¹+Y*J) := mul_le_mul_left'
        (add_le_add_left (le_mul_of_one_le_right (zero_le Y) jone) _) _
      _ = _ := by dsimp only [X]; ring
  apply kernelLp_exhaustion K hK hi D hD p hp.le _ _ f hf
  intro g hm hgi
  have result := kernel_interpolation_moment K hK D hD (W*J) (ENNReal.ofReal B) w strong g hm hgi p hp hp2
  have rr := ENNReal.rpow_le_rpow (result.trans (mul_le_mul_right' coef _)) ip
  rw [ENNReal.mul_rpow_of_nonneg _ _ ip,ENNReal.mul_rpow_of_nonneg _ _ ip] at rr
  have nonzero := (ENNReal.ofReal_pos.mpr hp0).ne'
  rw [eLpNorm_eq_lintegral_rpow_enorm nonzero ENNReal.ofReal_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm nonzero ENNReal.ofReal_ne_top,ENNReal.toReal_ofReal hp0.le]
  exact rr

end Burnett.Analysis.SignedFourierWindow
