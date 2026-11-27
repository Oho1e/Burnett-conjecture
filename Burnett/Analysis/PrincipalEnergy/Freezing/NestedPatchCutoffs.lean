import Burnett.Analysis.PrincipalEnergy.Freezing.RescaledPatchCutoff
import Mathlib.Tactic.Ring

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Set Metric Filter Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology

/-- The two nested windows are rescalings of the same fixed real profile.
The first equals one near the original patch, and the second equals one near
every point of the topological support of the first. -/
theorem exists_nested_patch_cutoffs (R : ℝ) (hR : 0 ≤ R) :
    ∃ (χ : CoordinateSpace → ℝ) (K : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ 0 ≤ K ∧
      (∀ (c : CoordinateSpace) (s : ℝ), 0 < s →
        let θ : CoordinateSpace → ℝ := fun x => χ (s⁻¹ • (x - c))
        ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
        (∀ x ∈ closedBall c ((R + 1) * s), θ x = 1) ∧
        tsupport θ ⊆ ball c ((R + 2) * s) ∧
        (∀ x ∈ ball c ((R + 1) * s), θ =ᶠ[𝓝 x] 1) ∧
        (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
        (∀ x, ‖θ x‖ ≤ 1 ∧ ‖fderiv ℝ θ x‖ ≤ K / s ∧
          ‖iteratedFDeriv ℝ 0 θ x‖ ≤ 1 ∧ ‖iteratedFDeriv ℝ 1 θ x‖ ≤ K / s ∧
          ‖iteratedFDeriv ℝ 2 θ x‖ ≤ K / s ^ 2)) ∧
      ∀ (c : CoordinateSpace) (ℓ : ℝ), 0 < ℓ →
        let θ : CoordinateSpace → ℝ := fun x => χ (ℓ⁻¹ • (x - c))
        let Θ : CoordinateSpace → ℝ := fun x => χ ((2 * ℓ)⁻¹ • (x - c))
        (∀ x ∈ closedBall c (R * ℓ), θ =ᶠ[𝓝 x] 1) ∧
        (∀ x ∈ tsupport θ, Θ =ᶠ[𝓝 x] 1) := by
  obtain ⟨χ, K, hχ, hχc, hK, scaled⟩ :=
    exists_rescaled_patch_cutoff (R + 1) (R + 2) (by linarith) (by linarith)
  refine ⟨χ, K, hχ, hχc, hK, scaled, ?_⟩
  intro c ℓ hℓ θ Θ
  obtain ⟨_, _, _, support, near, _, _⟩ := scaled c ℓ hℓ
  have h₂ : 0 < 2 * ℓ := mul_pos (by norm_num) hℓ
  obtain ⟨_, _, _, _, near₂, _, _⟩ := scaled c (2 * ℓ) h₂
  constructor
  · intro x hx
    exact near x (closedBall_subset_ball (mul_lt_mul_of_pos_right (by linarith) hℓ) hx)
  · intro x hx
    have hScale : (R + 2) * ℓ ≤ (R + 1) * (2 * ℓ) := calc
      _ ≤ (2 * (R + 1)) * ℓ := mul_le_mul_of_nonneg_right (by linarith) hℓ.le
      _ = _ := by ring
    exact near₂ x (ball_subset_ball hScale (support hx))

end Burnett.A03
