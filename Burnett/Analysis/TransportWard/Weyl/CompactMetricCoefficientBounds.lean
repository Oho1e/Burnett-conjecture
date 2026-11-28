import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient

/-! Smoothness of the actual field coefficient gives the uniform derivative
premises for its principal remainder on compact nonsingular field ranges. -/

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.V03

open Set Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

private theorem exists_iteratedFDeriv_bound_on_compact (F : V → W)
    {U K : Set V} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hK : IsCompact K) (hKU : K ⊆ U) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ G ∈ K, ‖iteratedFDeriv ℝ n F G‖ ≤ M := by
  have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hc : ContinuousOn (iteratedFDeriv ℝ n F) U :=
    (hF.continuousOn_iteratedFDerivWithin hn hU.uniqueDiffOn).congr
      (fun G hG => (iteratedFDerivWithin_of_isOpen n hU hG).symm)
  obtain ⟨B, hB⟩ := hK.bddAbove_image (hc.norm.mono hKU)
  exact ⟨max B 0, le_max_right _ _, fun G hG =>
    (hB (mem_image_of_mem _ hG)).trans (le_max_left _ _)⟩

private theorem norm_secondFDeriv_eq_iteratedFDeriv (F : V → W) (g : V) :
    ‖secondFDeriv F g‖ = ‖iteratedFDeriv ℝ 2 F g‖ := by
  have h₀ := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ F) (x := g) (n := 0)
  have h₁ := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := g) (n := 1)
  have h₀' : ‖secondFDeriv F g‖ = ‖iteratedFDeriv ℝ 1 (fderiv ℝ F) g‖ := by
    simpa only [norm_iteratedFDeriv_zero] using h₀
  exact h₀'.trans h₁

private theorem norm_thirdFDeriv_apply_le (F : V → W) (x u v w : V) :
    ‖thirdFDeriv F x u v w‖ ≤ ‖iteratedFDeriv ℝ 3 F x‖ * ‖u‖ * ‖v‖ * ‖w‖ := by
  have h : iteratedFDeriv ℝ 3 F x ![u, v, w] = thirdFDeriv F x u v w := by
    rw [iteratedFDeriv_succ_apply_right (n := 2), iteratedFDeriv_two_apply]
    rfl
  have hnorm := (iteratedFDeriv ℝ 3 F x).le_opNorm (![u, v, w] : Fin 3 → V)
  simpa [Fin.prod_univ_succ, h, mul_assoc] using hnorm

theorem exists_field_derivative_bounds_on_compact (F : V → W)
    {U K : Set V} (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ G ∈ K,
      ‖fderiv ℝ F G‖ ≤ M ∧ ‖secondFDeriv F G‖ ≤ M ∧
      ∀ u v w, ‖thirdFDeriv F G u v w‖ ≤ M * ‖u‖ * ‖v‖ * ‖w‖ := by
  obtain ⟨M₁, h₁, hM₁⟩ := exists_iteratedFDeriv_bound_on_compact F hU hF hK hKU 1
  obtain ⟨M₂, h₂, hM₂⟩ := exists_iteratedFDeriv_bound_on_compact F hU hF hK hKU 2
  obtain ⟨M₃, h₃, hM₃⟩ := exists_iteratedFDeriv_bound_on_compact F hU hF hK hKU 3
  refine ⟨M₁ + M₂ + M₃, by positivity, ?_⟩
  intro G hG
  have hD := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := F) (x := G) (n := 0)
  rw [norm_iteratedFDeriv_zero] at hD
  refine ⟨hD.le.trans ((hM₁ G hG).trans (by linarith)),
    (norm_secondFDeriv_eq_iteratedFDeriv F G).le.trans ((hM₂ G hG).trans (by linarith)), ?_⟩
  intro u v w
  refine (norm_thirdFDeriv_apply_le F G u v w).trans ?_
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ((hM₃ G hG).trans (by linarith)) (norm_nonneg _))
    (norm_nonneg _)) (norm_nonneg _)

theorem exists_field_family_derivative_bounds_on_compact {ι : Type*} [Fintype ι] (F : ι → V → W)
    {U K : Set V} (hU : IsOpen U) (hF : ∀ j, ContDiffOn ℝ ∞ (F j) U)
    (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ j, ∀ G ∈ K,
      ‖fderiv ℝ (F j) G‖ ≤ M ∧ ‖secondFDeriv (F j) G‖ ≤ M ∧
      ∀ u v w, ‖thirdFDeriv (F j) G u v w‖ ≤ M * ‖u‖ * ‖v‖ * ‖w‖ := by
  classical
  choose M hM hB using fun j => exists_field_derivative_bounds_on_compact (F j) hU (hF j) hK hKU
  refine ⟨∑ j, M j, Finset.sum_nonneg (fun j _ => hM j), ?_⟩
  intro j G hG
  have hj : M j ≤ ∑ j, M j := Finset.single_le_sum (fun j _ => hM j) (Finset.mem_univ j)
  obtain ⟨h₁, h₂, h₃⟩ := hB j G hG
  refine ⟨h₁.trans hj, h₂.trans hj, fun u v w => (h₃ u v w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hj (norm_nonneg _)) (norm_nonneg _)) (norm_nonneg _)

/-- On a fixed compact nonsingular range there is one coefficient constant for
every background and perturbation whose actual segment stays in that range. -/
theorem exists_metricPrincipalRemainder_uniform_bounds {ι X : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    (S : ι → Mat) (s t : ActionSlot ι) {K : Set Mat} (hK : IsCompact K)
    (hKdet : K ⊆ nonsingularMetricDomain) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (g h : X → Mat) (x : X),
      DifferentiableAt ℝ g x → DifferentiableAt ℝ h x →
      (∀ u ∈ Icc (0 : ℝ) 1, fieldSegment (g x) (h x) u ∈ K) →
      ‖principalCoefficientRemainder (metricActionCoefficient S s t) (g x) (h x)‖ ≤
        M * ‖h x‖^2 ∧
      ‖fderiv ℝ (fun y => principalCoefficientRemainder (metricActionCoefficient S s t) (g y) (h y)) x‖ ≤
        M * ‖h x‖^2 * ‖fderiv ℝ g x‖ + M * ‖h x‖ * ‖fderiv ℝ h x‖ := by
  obtain ⟨M, hM, hf⟩ := exists_field_derivative_bounds_on_compact (metricActionCoefficient S s t)
    isOpen_nonsingularMetricDomain (contDiffOn_metricActionCoefficient S s t) hK hKdet
  refine ⟨M, hM, fun g h x hg hh hseg => ?_⟩
  refine metricPrincipalRemainder_pointwise_bounds S s t g h x hg hh
    (fun u hu => hKdet (hseg u hu)) (fun u hu => (hf _ (hseg u hu)).2.1) hM ?_
  intro u hu v
  simpa only [pow_two, mul_assoc] using (hf _ (hseg u hu)).2.2 (h x) (h x) v

end Burnett.V03
