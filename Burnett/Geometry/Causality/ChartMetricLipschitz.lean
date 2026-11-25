import Burnett.Geometry.Causality.ChartTimeOrientation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open scoped BigOperators ContDiff Manifold
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

private theorem bilinear_coordinate_sum (B : LinearMap.BilinForm ℝ E) (u v : E) :
    B u v = ∑ i, ∑ j, B (coordinateBasis i) (coordinateBasis j) * (u i * v j) := by
  have hu : u = ∑ i, u i • coordinateBasis i := (coordinateBasis.sum_repr u).symm
  have hv : v = ∑ j, v j • coordinateBasis j := (coordinateBasis.sum_repr v).symm
  calc
    _ = B (∑ i, u i • coordinateBasis i) (∑ j, v j • coordinateBasis j) := congrArg₂ (fun a b => B a b) hu hv
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- On a compact convex subset of an actual chart, variation of the smooth
metric is Lipschitz as a bilinear form, uniformly over the test vectors. -/
theorem chart_metric_lipschitz_on_compact_convex {g : Field (M := M)}
    (hg : IsSmooth g) (c : M) {K : Set E} (hK : IsCompact K) (hc : Convex ℝ K)
    (hTarget : K ⊆ (chartAt E c).target) :
    ∃ L ≥ (0 : ℝ), ∀ x ∈ K, ∀ y ∈ K, ∀ u v : E,
      |coordinateBilinear g c x u v - coordinateBilinear g c y u v| ≤ L * ‖x - y‖ * ‖u‖ * ‖v‖ := by
  let B := coordinateBilinear g c
  let F (i j : Index) (y : E) := B y (coordinateBasis i) (coordinateBasis j)
  have hCoeff (i j : Index) : ∃ R ≥ (0 : ℝ), ∀ x ∈ K, ∀ y ∈ K,
      |F i j x - F i j y| ≤ R * ‖x - y‖ := by
    have hF := contDiffOn_coordinateBilinear_apply g hg c (coordinateBasis i) (coordinateBasis j)
    have hOpen := (chartAt E c).open_target
    have hDeriv : ContinuousOn (fun x => ‖fderiv ℝ (F i j) x‖) K :=
      (hF.continuousOn_fderiv_of_isOpen hOpen (by simp)).norm.mono hTarget
    obtain ⟨R, hR⟩ := hK.bddAbove_image hDeriv
    refine ⟨max R 0, le_max_right _ _, fun x hx y hy => ?_⟩
    have hdiff (q : E) (hq : q ∈ K) : DifferentiableAt ℝ (F i j) q :=
      (hF.contDiffAt (hOpen.mem_nhds (hTarget hq))).differentiableAt (by simp)
    have hBound (q : E) (hq : q ∈ K) : ‖fderiv ℝ (F i j) q‖ ≤ max R 0 :=
      (hR (mem_image_of_mem _ hq)).trans (le_max_left _ _)
    simpa only [Real.norm_eq_abs] using hc.norm_image_sub_le_of_norm_fderiv_le hdiff hBound hy hx
  choose R hR0 hR using hCoeff
  refine ⟨∑ i, ∑ j, R i j, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hR0 i j)), ?_⟩
  intro x hx y hy u v
  calc
    _ = |∑ i, ∑ j, (F i j x - F i j y) * (u i * v j)| := by
      change |B x u v - B y u v| = _
      simp only [bilinear_coordinate_sum (B x) u v, bilinear_coordinate_sum (B y) u v, F,
        sub_mul, Finset.sum_sub_distrib]
    _ ≤ ∑ i, ∑ j, |(F i j x - F i j y) * (u i * v j)| := by
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      exact Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i, ∑ j, R i j * ‖x - y‖ * ‖u‖ * ‖v‖ := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      have hu : |u i| ≤ ‖u‖ := (Real.norm_eq_abs (u i)) ▸ PiLp.norm_apply_le u i
      have hv : |v j| ≤ ‖v‖ := (Real.norm_eq_abs (v j)) ▸ PiLp.norm_apply_le v j
      rw [abs_mul, abs_mul, ← mul_assoc]
      exact mul_le_mul (mul_le_mul (hR i j x hx y hy) hu (abs_nonneg _)
        (mul_nonneg (hR0 i j) (norm_nonneg _))) hv (abs_nonneg _)
        (mul_nonneg (mul_nonneg (hR0 i j) (norm_nonneg _)) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_mul]

end Burnett.Geometry.FiniteCausalVolume
