import Mathlib.Analysis.Normed.Operator.Completeness
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith

/-!
# From dense scalar tests to an actual bounded linear limit

This is a conditional functional-analytic tool: the uniform operator-norm
bound is an explicit input. In particular, finite-order symbol seminorm
bounds in F05 do not by themselves provide a uniform C⁰/sup-norm bound,
nor does this file construct a pseudodifferential limit or its measure.
-/

noncomputable section

namespace Burnett.Analysis.Compactness

open Filter Metric Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem denseTests_apply_dist_le (u : ℕ → E →L[ℝ] ℝ) {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C) (n : ℕ) (x y : E) :
    dist (u n x) (u n y) ≤ C * dist x y := by
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact ((u n).le_opNorm (x - y)).trans
    (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _))

/-- Convergence on a dense set and one uniform operator bound force the
values at every point to be Cauchy. No limit map is assumed here. -/
theorem cauchySeq_all_of_dense_tests (u : ℕ → E →L[ℝ] ℝ) {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C) {D : Set E} (hD : Dense D)
    (hconv : ∀ x ∈ D, ∃ r : ℝ, Tendsto (fun n => u n x) atTop (𝓝 r))
    (x : E) : CauchySeq (fun n => u n x) := by
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hu 0)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := ε / (4 * (C + 1))
  have hden : 0 < 4 * (C + 1) := by positivity
  have hδ : 0 < δ := div_pos hε hden
  obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x hδ
  obtain ⟨r, hr⟩ := hconv y hy
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hr.cauchySeq (ε/2) (by positivity)
  have hδmul : δ * (4 * (C + 1)) = ε := div_mul_cancel₀ ε hden.ne'
  have hsmall : 2 * (C * δ) < ε / 2 := by nlinarith
  have hbound (k : ℕ) : dist (u k x) (u k y) ≤ C * δ :=
    (denseTests_apply_dist_le u hu k x y).trans
      (mul_le_mul_of_nonneg_left hxy.le hC)
  refine ⟨N, ?_⟩
  intro m hm n hn
  have hmiddle := hN m hm n hn
  have hlast : dist (u n y) (u n x) ≤ C * δ := by
    simpa only [dist_comm] using hbound n
  calc
    dist (u m x) (u n x) ≤ dist (u m x) (u m y) + dist (u m y) (u n x) :=
      dist_triangle _ _ _
    _ ≤ dist (u m x) (u m y) + (dist (u m y) (u n y) + dist (u n y) (u n x)) :=
      add_le_add_left (dist_triangle _ _ _) _
    _ ≤ C * δ + (dist (u m y) (u n y) + C * δ) :=
      add_le_add (hbound m) (add_le_add_left hlast _)
    _ < ε := by linarith

/-- The actual scalar pointwise limit exists on the whole normed space. -/
theorem exists_pointwise_limit_of_dense_tests (u : ℕ → E →L[ℝ] ℝ) {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C) {D : Set E} (hD : Dense D)
    (hconv : ∀ x ∈ D, ∃ r : ℝ, Tendsto (fun n => u n x) atTop (𝓝 r)) :
    ∃ L : E → ℝ, ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (L x)) := by
  choose L hL using fun x => cauchySeq_tendsto_of_complete
    (cauchySeq_all_of_dense_tests u hu hD hconv x)
  exact ⟨L, hL⟩

/-- A bounded continuous linear limit is constructed, with the original
uniform bound. Its uniqueness already follows from values on the dense
set, rather than requiring agreement on the whole space as an input. -/
theorem exists_unique_bounded_limit_of_dense_tests (u : ℕ → E →L[ℝ] ℝ) {C : ℝ}
    (hu : ∀ n, ‖u n‖ ≤ C) {D : Set E} (hD : Dense D)
    (hconv : ∀ x ∈ D, ∃ r : ℝ, Tendsto (fun n => u n x) atTop (𝓝 r)) :
    ∃ L : E →L[ℝ] ℝ, ‖L‖ ≤ C ∧
      (∀ x, Tendsto (fun n => u n x) atTop (𝓝 (L x))) ∧
      ∀ M : E →L[ℝ] ℝ,
        (∀ x ∈ D, Tendsto (fun n => u n x) atTop (𝓝 (M x))) → M = L := by
  obtain ⟨l, hl⟩ := exists_pointwise_limit_of_dense_tests u hu hD hconv
  have hbounded : Bornology.IsBounded (Set.range u) :=
    isBounded_iff_forall_norm_le.mpr ⟨C, by
      rintro _ ⟨n, rfl⟩
      exact hu n⟩
  let L : E →L[ℝ] ℝ := ContinuousLinearMap.ofTendstoOfBoundedRange l u
    (tendsto_pi_nhds.mpr hl) hbounded
  have hL (x : E) : Tendsto (fun n => u n x) atTop (𝓝 (L x)) := hl x
  have hC : 0 ≤ C := (norm_nonneg (u 0)).trans (hu 0)
  have hnorm : ‖L‖ ≤ C := by
    apply L.opNorm_le_bound hC
    intro x
    apply le_of_tendsto (hL x).norm
    exact Eventually.of_forall (fun n =>
      ((u n).le_opNorm x).trans (mul_le_mul_of_nonneg_right (hu n) (norm_nonneg _)))
  refine ⟨L, hnorm, hL, ?_⟩
  intro M hM
  apply ContinuousLinearMap.coeFn_injective
  apply hD.denseRange_val.equalizer M.continuous L.continuous
  funext x
  exact tendsto_nhds_unique (hM x x.property) (hL x)

/-- Eventual nonnegativity is closed under the actual pointwise limit.
The set P may be a cone of nonnegative tests; no PDO positivity is assumed
or constructed by this statement. -/
theorem pointwise_limit_nonneg_on (u : ℕ → E →L[ℝ] ℝ) (L : E →L[ℝ] ℝ)
    (hL : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (L x))) {P : Set E}
    (hpos : ∀ x ∈ P, ∀ᶠ n in atTop, 0 ≤ u n x) : ∀ x ∈ P, 0 ≤ L x := by
  intro x hx
  exact ge_of_tendsto (hL x) (hpos x hx)

/-- The common Gårding-shaped scalar situation: an explicit error tending
to zero and a lower bound -error imply nonnegativity of the limit value. -/
theorem pointwise_limit_nonneg_of_vanishing_error
    (u : ℕ → E →L[ℝ] ℝ) (L : E →L[ℝ] ℝ)
    (hL : ∀ x, Tendsto (fun n => u n x) atTop (𝓝 (L x))) {P : Set E}
    (err : ℕ → E → ℝ)
    (herr : ∀ x ∈ P, Tendsto (fun n => err n x) atTop (𝓝 0))
    (hpos : ∀ x ∈ P, ∀ᶠ n in atTop, -err n x ≤ u n x) : ∀ x ∈ P, 0 ≤ L x := by
  intro x hx
  have h := le_of_tendsto_of_tendsto (herr x hx).neg (hL x) (hpos x hx)
  simpa only [neg_zero] using h

end Burnett.Analysis.Compactness
