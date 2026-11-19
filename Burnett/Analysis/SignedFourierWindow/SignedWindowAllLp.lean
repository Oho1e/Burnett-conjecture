import Burnett.Analysis.SignedFourierWindow.WindowReflection
import Burnett.Analysis.SignedFourierWindow.KernelBilinearDual

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory
open scoped ENNReal

/-- Uniform strong Lᵖ inequalities for all finite exponents above one, for the
original kernels and all complex Lᵖ inputs. -/
theorem signed_window_all_Lp (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p : ℝ) (hp : 1<p) :
    ∃ V : ℝ≥0∞, V < ⊤ ∧ ∀ t : ℝ, 0<t → ∀ (q : Space) (I : Finset ℕ) (c : ℕ → ℂ),
      (∀ k, ‖c k‖ ≤ 1) → ∀ f : Space → ℂ, MemLp f (ENNReal.ofReal p) volume →
      let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
      eLpNorm (kernelApply K f) (ENNReal.ofReal p) volume ≤
        (V*ENNReal.ofReal (1+‖q‖))*eLpNorm f (ENNReal.ofReal p) volume := by
  have factor (q : Space) (r : ℝ) (hr : 1≤r) : (ENNReal.ofReal (1+‖q‖))^(1/r) ≤ ENNReal.ofReal (1+‖q‖) := by
    have h := ENNReal.rpow_le_rpow_of_exponent_le (show (1 : ℝ≥0∞) ≤ ENNReal.ofReal (1+‖q‖) by simp)
      (one_div_le_one_div_of_le zero_lt_one hr)
    simpa using h
  rcases lt_trichotomy p 2 with low|rfl|upper
  · obtain ⟨V,fin,h⟩ := signed_window_lower_Lp a ha cut p hp low
    refine ⟨V,fin,?_⟩
    intro t ht q I c hc f hf
    exact (h t ht q I c hc f hf).trans (mul_le_mul_right' (mul_le_mul_left' (factor _ _ hp.le) _) _)
  · let B := 2*SchwartzMap.seminorm ℝ 0 0 a
    have hB : 0 ≤ B := mul_nonneg (by norm_num) (apply_nonneg _ _)
    obtain ⟨_,_,h⟩ := signed_window_operator_estimates a ha cut
    refine ⟨ENNReal.ofReal B,ENNReal.ofReal_lt_top,?_⟩
    intro t ht q I c hc f hf
    obtain ⟨_,_,h2,_⟩ := finite_kernel_regular ((SchwartzMap.fourierTransformCLE ℂ).symm a) t ht q I c
    have h₂ : MemLp f 2 volume := by simpa using hf
    have bound := kernelApply_L2_extension _ h2 B hB (h t ht q I c hc).2 f h₂
    simpa using bound.trans (mul_le_mul_right' (le_mul_of_one_le_right (zero_le _) (by simp : (1:ℝ≥0∞) ≤ ENNReal.ofReal (1+‖q‖))) _)
  · let r := p/(p-1)
    have den : 0<p-1 := by linarith
    have hr : 1<r := (lt_div_iff₀ den).mpr (by linarith)
    have hr2 : r<2 := (div_lt_iff₀ den).mpr (by linarith)
    obtain ⟨V,fin,h⟩ := reflected_window_lower_Lp a ha cut r hr hr2
    refine ⟨V,fin,?_⟩
    intro t ht q I c hc f hf
    let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
    obtain ⟨hK,hi,_,D,hD⟩ := finite_kernel_regular ((SchwartzMap.fourierTransformCLE ℂ).symm a) t ht q I c
    have estimate := kernelLp_of_reflected_conjugate K hK hi D hD p upper
      (V*(ENNReal.ofReal (1+‖q‖))^(1/r)) (h t ht q I c hc) f hf
    exact estimate.trans (mul_le_mul_right' (mul_le_mul_left' (factor _ _ hr.le) _) _)

end Burnett.Analysis.SignedFourierWindow
