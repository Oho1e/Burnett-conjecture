import Burnett.Analysis.SignedFourierWindow.SignedWindowLowerLp

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Finset
open scoped FourierTransform ENNReal

def reflectedWindow (a : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (LinearIsometryEquiv.neg ℝ (E := Space)) a

/-- Reflecting the physical convolution kernel reflects the frequency window
and reverses the modulation vector; the complex coefficients stay in the same slots. -/
theorem reflected_window_kernel (a : SchwartzMap Space ℂ) (t : ℝ) (q : Space) (I : Finset ℕ)
    (c : ℕ → ℂ) (z : Space) :
    finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm (reflectedWindow a)) t (-q) I c z =
      finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c (-z) := by
  have inv (v : Space) : (SchwartzMap.fourierTransformCLE ℂ).symm (reflectedWindow a) v =
      (SchwartzMap.fourierTransformCLE ℂ).symm a (-v) := by
    change 𝓕 ((a : Space → ℂ) ∘ LinearIsometryEquiv.neg ℝ) (-v) = 𝓕 (a : Space → ℂ) (- -v)
    exact Real.fourierIntegral_comp_linearIsometry _ _ _
  unfold finiteWindowKernel shiftedSpatialKernel
  apply sum_congr rfl
  intro i _
  rw [inv]
  simp only [smul_neg,neg_add_rev,neg_neg]
  rw [add_comm q]

theorem reflected_window_lower_Lp (a : SchwartzMap Space ℂ) (ha : HasCompactSupport (a : Space → ℂ))
    (cut : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2) (p : ℝ) (hp : 1<p) (hp2 : p<2) :
    ∃ V : ℝ≥0∞, V < ⊤ ∧ ∀ t : ℝ, 0<t → ∀ (q : Space) (I : Finset ℕ) (c : ℕ → ℂ),
      (∀ k, ‖c k‖ ≤ 1) → ∀ f : Space → ℂ, MemLp f (ENNReal.ofReal p) volume →
      let K := finiteWindowKernel ((SchwartzMap.fourierTransformCLE ℂ).symm a) t q I c
      eLpNorm (kernelApply (fun z => K (-z)) f) (ENNReal.ofReal p) volume ≤
        (V*(ENNReal.ofReal (1+‖q‖))^(1/p))*eLpNorm f (ENNReal.ofReal p) volume := by
  let b := reflectedWindow a
  have full : HasCompactSupport (b : Space → ℂ) := ha.comp_homeomorph (LinearIsometryEquiv.neg ℝ (E := Space)).toHomeomorph
  have ann (ξ : Space) (h : b ξ ≠ 0) := cut (-ξ) h
  obtain ⟨V,fin,est⟩ := signed_window_lower_Lp b full (fun ξ h => by simpa only [norm_neg] using ann ξ h) p hp hp2
  refine ⟨V,fin,?_⟩
  intro t ht q I c hc f hf
  have eq := funext (reflected_window_kernel a t q I c)
  simpa only [b,eq,norm_neg] using est t ht (-q) I c hc f hf

end Burnett.Analysis.SignedFourierWindow
