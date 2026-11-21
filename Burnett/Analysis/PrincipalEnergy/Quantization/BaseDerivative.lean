import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderSymbol
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff

/-- The first base derivative is of order one as a function of frequency.
These are precisely the mixed derivative bounds used for the target-variable kernel estimate. -/
structure FirstBaseFrequencyOrderOne (a : E → E → ℂ) : Prop where
  frequency : FrequencyOrderOne a
  baseDiff : ∀ (n : ℕ) (ξ : E), Differentiable ℝ (fun x => iteratedFDeriv ℝ n (a x) ξ)
  order : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
    ‖fderiv ℝ (fun y => iteratedFDeriv ℝ n (a y) ξ) x‖ * (1 + ‖ξ‖) ^ n ≤ C * (1 + ‖ξ‖)

/-- This estimate controls the actual change of the frequency derivative when
the base point moves. The constant remains the symbol seminorm of this order. -/
theorem exists_frequencyDerivative_baseDifference_bound {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (n : ℕ) : ∃ C : ℝ, 0 ≤ C ∧ ∀ x y ξ,
    ‖iteratedFDeriv ℝ n (a x) ξ - iteratedFDeriv ℝ n (a y) ξ‖ * (1 + ‖ξ‖) ^ n ≤
      C * ‖x-y‖ * (1 + ‖ξ‖) := by
  obtain ⟨C,hC,hBound⟩ := ha.order n
  refine ⟨C,hC,?_⟩
  intro x y ξ
  let W := 1 + ‖ξ‖
  have hW : 0 < W := by unfold W; positivity
  have hDiff (z : E) : ‖fderiv ℝ (fun t => iteratedFDeriv ℝ n (a t) ξ) z‖ ≤ C * W / W^n :=
    (le_div_iff₀ (pow_pos hW _)).mpr (hBound z ξ)
  have hMv := Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => ha.baseDiff n ξ z) (fun z _ => hDiff z) convex_univ (mem_univ y) (mem_univ x)
  change ‖iteratedFDeriv ℝ n (a x) ξ - iteratedFDeriv ℝ n (a y) ξ‖ * W ^ n ≤ C * ‖x-y‖ * W
  refine (mul_le_mul_of_nonneg_right hMv (pow_nonneg hW.le _)).trans_eq ?_
  field_simp [hW.ne']

end Burnett.Analysis.FirstOrderDyadic
