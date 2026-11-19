import Burnett.Analysis.SignedFourierWindow.CalderonFiniteKernel
import Burnett.Analysis.SignedFourierWindow.CalderonWeakType

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory
open scoped NNReal ENNReal

/-- Uniform weak (1,1) for the actual modulated finite dyadic sums. All positive
starting scales and all unit-disc coefficients are allowed. The shift costs at most
one power. Every integrable input is covered, irrespective of its representative. -/
theorem signed_window_weak_one (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) :
    ∃ U : ℝ≥0∞, U < ⊤ ∧ ∀ (t : ℝ), 0 < t → ∀ (q : Space) (I : Finset ℕ) (c : ℕ → ℂ),
      (∀ k, ‖c k‖ ≤ 1) → ∀ (f : Space → ℂ), Integrable f → ∀ (level : ℝ≥0), 0 < level →
      let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
      (level : ℝ≥0∞) * volume {x | (level : ℝ≥0∞) < ‖kernelApply K f x‖ₑ} ≤
        (U*ENNReal.ofReal (1+‖q‖)) * ∫⁻ y, ‖f y‖ₑ := by
  obtain ⟨C,hC,est⟩ := signed_window_operator_estimates a ha cut
  let B := 2*SchwartzMap.seminorm ℝ 0 0 a
  have hB : 0 ≤ B := mul_nonneg (by norm_num) (apply_nonneg _ _)
  let P := 4096+768*(ENNReal.ofReal B)^2
  let U := 2*(P+2*ENNReal.ofReal C)
  have uf : U < ⊤ := by dsimp only [U,P]; finiteness
  refine ⟨U,uf,?_⟩
  intro t ht q I c hc f hf level hl
  let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
  obtain ⟨hcont,hI,h2,D,hD⟩ := finite_kernel_regular ((SchwartzMap.fourierTransformCLE ℂ).symm a) t ht q I c
  obtain ⟨hA,test⟩ := est t ht q I c hc
  let g := hf.1.mk f
  have hg : Measurable g := hf.1.stronglyMeasurable_mk.measurable
  have eq : f =ᵐ[volume] g := hf.1.ae_eq_mk
  have val (x : Space) : kernelApply K f x = kernelApply K g x :=
    integral_congr_ae (eq.mono fun y hy => congrArg (fun z => K (x-y)*z) hy)
  have mass : (∫⁻ y, ‖g y‖ₑ) = ∫⁻ y, ‖f y‖ₑ := lintegral_congr_ae (eq.symm.fun_comp (fun z => ‖z‖ₑ))
  let J := ENNReal.ofReal (1+‖q‖)
  have low : 1 ≤ J := by simp [J]
  have coeff : 2*(P+2*ENNReal.ofReal (C*(1+‖q‖))) ≤ U*J := by
    rw [ENNReal.ofReal_mul hC]
    change 2*(P+2*(ENNReal.ofReal C*J)) ≤ (2*(P+2*ENNReal.ofReal C))*J
    calc
      _ ≤ 2*(P*J+2*(ENNReal.ofReal C*J)) := mul_le_mul_left'
        (add_le_add_right (le_mul_of_one_le_right (zero_le _) low) _) _
      _ = _ := by ring
  have weak := kernel_weak_type K hcont h2 D hD B hB test _ (kernel_hormander_enorm K hI _ hA)
    g hg (hf.congr eq) level hl
  rw [mass] at weak
  change (level : ℝ≥0∞) * volume {x | (level : ℝ≥0∞) < ‖kernelApply K f x‖ₑ} ≤ _
  simp_rw [val]
  exact weak.trans (mul_le_mul_right' coeff _)

end Burnett.Analysis.SignedFourierWindow
