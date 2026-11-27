import Burnett.Geometry.ConnectionDifference
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Tactic.Linarith

set_option autoImplicit false
noncomputable section

namespace Burnett.A03

open Set Metric Filter Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology

private theorem scale_affine_iteratedFDeriv_le (χ : CoordinateSpace → ℝ)
    (hχ : ContDiff ℝ ∞ χ) (c : CoordinateSpace) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (n : ℕ) (x : CoordinateSpace) :
    ‖iteratedFDeriv ℝ n (fun y => χ (ℓ⁻¹ • (y - c))) x‖ ≤
      ‖iteratedFDeriv ℝ n χ (ℓ⁻¹ • (x - c))‖ / ℓ ^ n := by
  let D : CoordinateSpace →L[ℝ] CoordinateSpace := ℓ⁻¹ • ContinuousLinearMap.id ℝ CoordinateSpace
  have hD (y : CoordinateSpace) : D y = ℓ⁻¹ • y := rfl
  have hDn : ‖D‖ ≤ ℓ⁻¹ := D.opNorm_le_bound (inv_nonneg.mpr hℓ.le) (fun y => by
    rw [hD, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le)])
  have hComp : (fun y => χ (ℓ⁻¹ • (y - c))) = fun y => (χ ∘ D) (y - c) := rfl
  rw [hComp, iteratedFDeriv_comp_sub n c x,
    D.iteratedFDeriv_comp_right hχ (x - c) (by exact_mod_cast le_top)]
  calc
    _ ≤ ‖iteratedFDeriv ℝ n χ (D (x - c))‖ * ‖D‖ ^ n := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ n χ (D (x - c))).norm_compContinuousLinearMap_le (fun _ => D)
    _ ≤ ‖iteratedFDeriv ℝ n χ (D (x - c))‖ * (ℓ⁻¹) ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hDn _) (norm_nonneg _)
    _ = _ := by rw [hD, inv_pow, div_eq_mul_inv]

/-- Choose one compactly supported real profile and one derivative constant
before choosing the center and positive patch scale. The topological support
stays strictly inside the outer ball. -/
theorem exists_rescaled_patch_cutoff (inner outer : ℝ) (hInner : 0 < inner)
    (hOuter : inner < outer) :
    ∃ (χ : CoordinateSpace → ℝ) (K : ℝ),
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ 0 ≤ K ∧
      ∀ (c : CoordinateSpace) (ℓ : ℝ), 0 < ℓ →
        let θ : CoordinateSpace → ℝ := fun x => χ (ℓ⁻¹ • (x - c))
        ContDiff ℝ ∞ θ ∧ HasCompactSupport θ ∧
        (∀ x ∈ closedBall c (inner * ℓ), θ x = 1) ∧
        tsupport θ ⊆ ball c (outer * ℓ) ∧
        (∀ x ∈ ball c (inner * ℓ), θ =ᶠ[𝓝 x] 1) ∧
        (∀ x, 0 ≤ θ x ∧ θ x ≤ 1) ∧
        (∀ x, ‖θ x‖ ≤ 1 ∧ ‖fderiv ℝ θ x‖ ≤ K / ℓ ∧
          ‖iteratedFDeriv ℝ 0 θ x‖ ≤ 1 ∧ ‖iteratedFDeriv ℝ 1 θ x‖ ≤ K / ℓ ∧
          ‖iteratedFDeriv ℝ 2 θ x‖ ≤ K / ℓ ^ 2) := by
  let B : ContDiffBump (0 : CoordinateSpace) := ⟨inner, (inner + outer) / 2, hInner, by linarith⟩
  let χ : CoordinateSpace → ℝ := B
  have hχ : ContDiff ℝ ∞ χ := B.contDiff
  have hχc : HasCompactSupport χ := B.hasCompactSupport
  have uniform (n : ℕ) : ∃ M : ℝ, 0 ≤ M ∧ ∀ y, ‖iteratedFDeriv ℝ n χ y‖ ≤ M := by
    have hCont := (hχ.continuous_iteratedFDeriv (m := n) (by exact_mod_cast le_top)).norm
    have hComp := (hχc.iteratedFDeriv (𝕜 := ℝ) n).norm
    obtain ⟨y, hy⟩ := hCont.exists_forall_ge_of_hasCompactSupport hComp
    exact ⟨_, norm_nonneg _, hy⟩
  obtain ⟨K₁, hK₁, hb₁⟩ := uniform 1
  obtain ⟨K₂, _, hb₂⟩ := uniform 2
  let K := max K₁ K₂
  refine ⟨χ, K, hχ, hχc, hK₁.trans (le_max_left _ _), ?_⟩
  intro c ℓ hℓ θ
  have hSmooth : ContDiff ℝ ∞ θ :=
    hχ.comp ((contDiff_id.sub contDiff_const).const_smul ℓ⁻¹)
  have hScale (x : CoordinateSpace) :
      ‖ℓ⁻¹ • (x - c)‖ = dist x c / ℓ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hℓ.le), dist_eq_norm, div_eq_inv_mul]
  have hOne (x : CoordinateSpace) (hx : x ∈ closedBall c (inner * ℓ)) : θ x = 1 := by
    change B (ℓ⁻¹ • (x - c)) = 1
    apply B.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, hScale]
    exact (div_le_iff₀ hℓ).mpr (mem_closedBall.mp hx)
  have hClosed : tsupport θ ⊆ closedBall c (((inner + outer) / 2) * ℓ) := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    change ℓ⁻¹ • (x - c) ∈ Function.support B at hx
    rw [B.support_eq, mem_ball, dist_zero_right, hScale] at hx
    exact mem_closedBall.mpr ((div_le_iff₀ hℓ).mp (le_of_lt hx))
  have hCompact : HasCompactSupport θ :=
    (isCompact_closedBall c _).of_isClosed_subset isClosed_closure hClosed
  have hSupport : tsupport θ ⊆ ball c (outer * ℓ) :=
    hClosed.trans (closedBall_subset_ball (mul_lt_mul_of_pos_right (by linarith) hℓ))
  have hNear (x : CoordinateSpace) (hx : x ∈ ball c (inner * ℓ)) : θ =ᶠ[𝓝 x] 1 :=
    mem_of_superset (isOpen_ball.mem_nhds hx) fun y hy => hOne y (ball_subset_closedBall hy)
  have hRange (x : CoordinateSpace) : 0 ≤ θ x ∧ θ x ≤ 1 := ⟨B.nonneg, B.le_one⟩
  refine ⟨hSmooth, hCompact, hOne, hSupport, hNear, hRange, ?_⟩
  intro x
  have hValue : ‖θ x‖ ≤ 1 := by
    rw [Real.norm_of_nonneg (hRange x).1]
    exact (hRange x).2
  have h0 : ‖iteratedFDeriv ℝ 0 θ x‖ ≤ 1 := by
    rw [norm_iteratedFDeriv_zero]
    exact hValue
  have h1 : ‖iteratedFDeriv ℝ 1 θ x‖ ≤ K / ℓ := by
    have h := scale_affine_iteratedFDeriv_le χ hχ c ℓ hℓ 1 x
    rw [pow_one] at h
    exact h.trans (div_le_div_of_nonneg_right ((hb₁ _).trans (le_max_left _ _)) hℓ.le)
  have h2 : ‖iteratedFDeriv ℝ 2 θ x‖ ≤ K / ℓ ^ 2 :=
    (scale_affine_iteratedFDeriv_le χ hχ c ℓ hℓ 2 x).trans
      (div_le_div_of_nonneg_right ((hb₂ _).trans (le_max_right _ _)) (sq_nonneg ℓ))
  have hf : ‖fderiv ℝ θ x‖ ≤ K / ℓ := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := fderiv ℝ θ) (x := x)]
    exact (norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := θ) (x := x) (n := 0)).le.trans h1
  exact ⟨hValue, hf, h0, h1, h2⟩

end Burnett.A03
