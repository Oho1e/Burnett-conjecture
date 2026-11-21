import Burnett.Analysis.PrincipalEnergy.Localization.MovingPlateauFrequency

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform

private theorem norm_fderiv_complex_smul_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {f : Space → ℂ} {g : Space → F} {x : Space}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    ‖fderiv ℝ (fun y => f y • g y) x‖ ≤ ‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖ := by
  letI : NormedSpace ℂ (Space →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hR : ‖(fderiv ℝ f x).smulRight (g x)‖ ≤ ‖fderiv ℝ f x‖ * ‖g x‖ := by
    refine ((fderiv ℝ f x).smulRight (g x)).opNorm_le_bound (by positivity) fun y => ?_
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    exact (mul_le_mul_of_nonneg_right ((fderiv ℝ f x).le_opNorm y) (norm_nonneg _)).trans_eq (by ring)
  change ‖fderiv ℝ (f • g) x‖ ≤ _
  rw [fderiv_smul hf hg]
  exact (norm_add_le _ _).trans (add_le_add (by rw [norm_smul]) hR)

theorem exists_movingPlateauMixedIntegrand_derivative_bound {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (χ : SchwartzMap Space ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c x ξ η,
      ‖fderiv ℝ (fun y => sandwichFrequencyFactor χ y η • iteratedFDeriv ℝ n (a (y + c)) (ξ + η)) x‖ *
        (1 + ‖ξ‖)^n ≤ C * (1 + ‖ξ‖) *
          ((1 + ‖η‖)^(n + 2) * ‖𝓕 (χ : Space → ℂ) η‖) := by
  letI : NormedSpace ℂ (ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ) :=
    ContinuousMultilinearMap.normedSpace'
  obtain ⟨A, hA, orderA⟩ := ha.frequency.order n
  obtain ⟨B, hB, orderB⟩ := ha.order n
  let S := SchwartzMap.seminorm ℝ 0 0 χ
  let T := SchwartzMap.seminorm ℝ 0 1 χ + S * (2 * Real.pi)
  have hS : 0 ≤ S := (norm_nonneg _).trans (SchwartzMap.norm_le_seminorm ℝ χ (0 : Space))
  have hT : 0 ≤ T := add_nonneg (((norm_nonneg _).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ 1 (0 : Space))))
    (mul_nonneg hS (by positivity))
  refine ⟨S * B + T * A, by positivity, fun c x ξ η => ?_⟩
  let f := fun y => sandwichFrequencyFactor χ y η
  let g := fun y => iteratedFDeriv ℝ n (a (y + c)) (ξ + η)
  let F := 𝓕 (χ : Space → ℂ) η
  let W := 1 + ‖ξ‖
  let V := 1 + ‖η‖
  have hW : 0 ≤ W := by dsimp only [W]; positivity
  have hV : 1 ≤ V := le_add_of_nonneg_right (norm_nonneg _)
  have hf : DifferentiableAt ℝ f x :=
    (((contDiff_sandwichFrequencyFactor χ).comp
      ((contDiff_id : ContDiff ℝ ∞ (id : Space → Space)).prodMk contDiff_const)).differentiable (by simp)) x
  have hg : DifferentiableAt ℝ g x := (differentiableAt_comp_add_right c).mpr ((ha.baseDiff n (ξ + η)) (x + c))
  have ⟨hf₀, hf₁⟩ := sandwichFrequencyFactor_base_controls χ x η
  have hg₀ : ‖g x‖ * W^n ≤ A * W * V^(n + 1) :=
    shifted_frequency_order_weight_le (fun y ζ => iteratedFDeriv ℝ n (a y) ζ) n hA orderA (x + c) ξ η
  have hg₁ : ‖fderiv ℝ g x‖ * W^n ≤ B * W * V^(n + 1) := by
    rw [show fderiv ℝ g x = fderiv ℝ (fun y => iteratedFDeriv ℝ n (a y) (ξ + η)) (x + c) from
      fderiv_comp_add_right (f := fun y => iteratedFDeriv ℝ n (a y) (ξ + η)) (x := x) c]
    exact shifted_frequency_order_weight_le (fun y ζ => fderiv ℝ (fun z => iteratedFDeriv ℝ n (a z) ζ) y)
      n hB orderB (x + c) ξ η
  change ‖fderiv ℝ (fun y => f y • g y) x‖ * W^n ≤ (S * B + T * A) * W * (V^(n + 2) * ‖F‖)
  calc
    _ ≤ (‖f x‖ * ‖fderiv ℝ g x‖ + ‖fderiv ℝ f x‖ * ‖g x‖) * W^n :=
      mul_le_mul_of_nonneg_right (norm_fderiv_complex_smul_le hf hg) (pow_nonneg hW _)
    _ = ‖f x‖ * (‖fderiv ℝ g x‖ * W^n) + ‖fderiv ℝ f x‖ * (‖g x‖ * W^n) := by ring
    _ ≤ (S * ‖F‖) * (B * W * V^(n + 1)) + (T * V * ‖F‖) * (A * W * V^(n + 1)) :=
      add_le_add (mul_le_mul hf₀ hg₁ (mul_nonneg (norm_nonneg _) (pow_nonneg hW _)) (by positivity))
        (mul_le_mul hf₁ hg₀ (mul_nonneg (norm_nonneg _) (pow_nonneg hW _)) (by positivity))
    _ ≤ (S * ‖F‖) * (B * W * V^(n + 2)) + (T * V * ‖F‖) * (A * W * V^(n + 1)) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hV (Nat.le_succ _)) (mul_nonneg hB hW)) (by positivity)) _
    _ = _ := by rw [show n + 2 = (n + 1) + 1 from rfl, pow_succ V (n + 1)]; ring


end Burnett.Analysis.CarlesonEmbedding
