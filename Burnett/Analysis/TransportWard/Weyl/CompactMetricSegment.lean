import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option maxHeartbeats 2100000

noncomputable section

namespace Burnett.V03

open Filter Set Metric Burnett.Analysis.TransportWardSymbol
open scoped Topology Matrix.Norms.Elementwise

/-- A uniform norm modulus on a compact window, including an empty window. -/
theorem exists_compact_uniform_zero_norm_modulus {E F : Type*}
    [TopologicalSpace E] [NormedAddCommGroup F] {S : Set E} (hS : IsCompact S)
    (H : ℕ → E → F) (hH : ∀ n, ContinuousOn (H n) S)
    (hConv : TendstoUniformlyOn H (fun _ => 0) atTop S) :
    ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧ ∀ n x, x ∈ S → ‖H n x‖ ≤ ε n := by
  let L (n : ℕ) := insert (0 : ℝ) ((fun x => ‖H n x‖) '' S)
  let ε (n : ℕ) := sSup (L n)
  have hL (n : ℕ) : IsCompact (L n) := (hS.image_of_continuousOn (hH n).norm).insert 0
  have hb (n : ℕ) : BddAbove (L n) := (hL n).bddAbove
  have hε (n : ℕ) : 0 ≤ ε n := le_csSup (hb n) (mem_insert _ _)
  refine ⟨ε, hε, ?_, fun n x hx => le_csSup (hb n) (mem_insert_of_mem _ (mem_image_of_mem _ hx))⟩
  apply Metric.tendsto_nhds.2
  intro d hd
  have hd' : 0 < d / 2 := by positivity
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv (d / 2) hd'] with n hn
  rw [dist_zero_right, Real.norm_of_nonneg (hε n)]
  have hUpper : ε n ≤ d / 2 := by
    apply csSup_le (insert_nonempty _ _)
    intro v hv
    rcases (mem_insert_iff.mp hv) with rfl | ⟨x, hx, rfl⟩
    · exact hd'.le
    · exact (show ‖H n x‖ < d / 2 by simpa only [dist_zero_left, dist_zero_right] using hn x hx).le
  linarith

/-- All sufficiently late affine matrix segments lie in a single compact
nonsingular neighborhood of the original background matrix image. -/
theorem exists_eventually_compact_nonsingular_fieldSegments {E : Type*} [TopologicalSpace E]
    {W : Set E} (hW : IsCompact W) (G : E → Mat) (hG : ContinuousOn G W)
    (hDet : ∀ x ∈ W, G x ∈ nonsingularMetricDomain)
    (H : ℕ → E → Mat) (hConv : TendstoUniformlyOn H (fun _ => 0) atTop W) :
    ∃ K : Set Mat, IsCompact K ∧ K ⊆ nonsingularMetricDomain ∧
      ∀ᶠ n in atTop, ∀ x ∈ W, ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment (G x) (H n x) t ∈ K := by
  let S := G '' W
  have hS : IsCompact S := hW.image_of_continuousOn hG
  obtain ⟨d, hd, hNd⟩ := hS.exists_cthickening_subset_open isOpen_nonsingularMetricDomain
    (image_subset_iff.mpr hDet)
  let K := cthickening d S
  refine ⟨K, hS.cthickening, hNd, ?_⟩
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hConv d hd] with n hn
  intro x hx t ht
  apply mem_cthickening_of_dist_le _ (G x) d S (mem_image_of_mem _ hx)
  rw [dist_eq_norm, fieldSegment, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1]
  have hn' : ‖H n x‖ < d := by simpa only [dist_zero_left, dist_zero_right] using hn x hx
  exact (mul_le_of_le_one_left (norm_nonneg _) ht.2).trans hn'.le

end Burnett.V03
