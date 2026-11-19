import Burnett.Geometry.ActualChartSecondJet
import Burnett.Analysis.Sobolev.TestJet
import Burnett.Geometry.ChartVolume
import Mathlib.Topology.Compactness.Lindelof

/-!
Transport of smooth cutoffs and a countable cover by compactly nested coordinate windows.
-/

set_option autoImplicit false
noncomputable section

namespace Burnett.Microlocal.OverlapGradient

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry ChartVolume ConnectionDifference ManifoldMetric ActualChartSecondJet
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Transport the same cutoff to the target chart, extending it smoothly
by zero off the target overlap. -/
theorem exists_transportOverlapCutoff (c d : M) (χ : D)
    (hχ : tsupport (χ : CoordinateSpace → ℝ) ⊆ (chartTransition c d).source) :
    ∃ η : D, tsupport (η : CoordinateSpace → ℝ) ⊆ (chartTransition c d) '' tsupport (χ : CoordinateSpace → ℝ) ∧
      ∀ x ∈ (chartTransition c d).source, (η : CoordinateSpace → ℝ) (chartTransition c d x) = (χ : CoordinateSpace → ℝ) x := by
  let e := chartTransition c d
  let f : CoordinateSpace → ℝ := e.target.indicator ((χ : CoordinateSpace → ℝ) ∘ e.symm)
  have hK : IsCompact (e '' tsupport (χ : CoordinateSpace → ℝ)) :=
    (test_compactSupport χ).image_of_continuousOn (e.continuousOn.mono hχ)
  have hfS : tsupport f ⊆ e '' tsupport (χ : CoordinateSpace → ℝ) := by
    apply closure_minimal _ hK.isClosed
    intro y hy
    have hyt : y ∈ e.target := by
      by_contra hy'
      exact hy (Set.indicator_of_notMem hy' _)
    refine ⟨e.symm y, subset_tsupport _ ?_, e.right_inv hyt⟩
    change (χ : CoordinateSpace → ℝ) (e.symm y) ≠ 0
    change f y ≠ 0 at hy
    simpa only [f, Set.indicator_of_mem hyt, Function.comp_apply] using hy
  have hfTarget : tsupport f ⊆ e.target := hfS.trans (image_subset_iff.mpr (e.mapsTo.mono_left hχ))
  have hsymm : e.symm = chartTransition d c := by
    simp only [e, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hSmoothInverse : ContDiffOn ℝ ∞ (e.symm : CoordinateSpace → CoordinateSpace) e.target := by
    change ContDiffOn ℝ ∞ (e.symm : CoordinateSpace → CoordinateSpace) e.symm.source
    rw [hsymm]
    exact contDiffOn_chartTransition_infty d c
  have hf : ContDiff ℝ ∞ f := by
    have hLoc := ((test_smooth χ).comp_contDiffOn hSmoothInverse).congr
      (fun y hy => Set.indicator_of_mem hy _)
    apply contDiff_iff_contDiffAt.mpr
    intro y
    by_cases hy : y ∈ e.target
    · exact hLoc.contDiffAt (e.open_target.mem_nhds hy)
    · have hs : y ∉ tsupport f := fun hy' => hy (hfTarget hy')
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : CoordinateSpace => (0 : ℝ)) y).congr_of_eventuallyEq
      exact notMem_tsupport_iff_eventuallyEq.mp hs
  refine ⟨⟨f, hf, hK.of_isClosed_subset isClosed_closure hfS⟩, hfS, ?_⟩
  intro x hx
  change e.target.indicator ((χ : CoordinateSpace → ℝ) ∘ e.symm) (e x) = _
  rw [Set.indicator_of_mem (e.mapsTo hx), Function.comp_apply, e.left_inv hx]

end Burnett.Microlocal.OverlapGradient

namespace Burnett.Microlocal.OverlapWindows

open Set Filter
open scoped Manifold Topology
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference

private theorem exists_ball_windows {X : Type*} [PseudoMetricSpace X]
    (e : OpenPartialHomeomorph X X) (x : X) (hx : x ∈ e.source)
    (U V : Set X) (hU : U ∈ 𝓝 x) (hV : V ∈ 𝓝 (e x)) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ Metric.closedBall x s ⊆ e.source ∩ U ∧
      Metric.closedBall (e x) t ⊆ e.target ∩ V ∧ MapsTo e (Metric.closedBall x s) (Metric.ball (e x) t) := by
  obtain ⟨t, ht, htarget⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (e.open_target.mem_nhds (e.map_source hx)) hV)
  have hpre : e ⁻¹' Metric.ball (e x) t ∈ 𝓝 x :=
    (e.continuousAt hx) (Metric.ball_mem_nhds _ ht)
  obtain ⟨s, hs, hsource⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
    (inter_mem (inter_mem (e.open_source.mem_nhds hx) hU) hpre)
  exact ⟨s, t, hs, ht, fun _ hy => (hsource hy).1, htarget, fun _ hy => (hsource hy).2⟩

/-- Around an overlap point one may prescribe neighborhoods in both
coordinate charts. A positive-radius closed source ball then maps into
the interior of a closed target ball lying in the requested target window. -/
theorem exists_chartTransition_ball_windows {M : Type*} [TopologicalSpace M]
    [ChartedSpace CoordinateSpace M] (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source)
    (U V : Set CoordinateSpace) (hU : U ∈ 𝓝 x) (hV : V ∈ 𝓝 (chartTransition c d x)) :
    ∃ s t : ℝ, 0 < s ∧ 0 < t ∧
      Metric.closedBall x s ⊆ (chartTransition c d).source ∩ U ∧
      Metric.closedBall (chartTransition c d x) t ⊆ (chartTransition c d).target ∩ V ∧
      MapsTo (chartTransition c d) (Metric.closedBall x s) (Metric.ball (chartTransition c d x) t) :=
  exists_ball_windows (chartTransition c d) x hx U V hU hV

end Burnett.Microlocal.OverlapWindows

namespace Burnett.Microlocal.OverlapWindows

open Set Filter
open scoped Manifold Topology
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference

/-- For an actual pair of charts, choose source and target balls before
subsequence extraction. Even the open half-radius source balls of a
countable subfamily cover the overlap. -/
theorem exists_countable_chartTransition_windows {M : Type*} [TopologicalSpace M]
    [ChartedSpace CoordinateSpace M] (c d : M)
    (U V : (chartTransition c d).source → Set CoordinateSpace)
    (hU : ∀ x, U x ∈ 𝓝 x.val) (hV : ∀ x, V x ∈ 𝓝 (chartTransition c d x.val)) :
    ∃ (s t : (chartTransition c d).source → ℝ) (centers : Set (chartTransition c d).source),
      centers.Countable ∧
      (∀ x, 0 < s x ∧ 0 < t x ∧
        Metric.closedBall x.val (s x) ⊆ (chartTransition c d).source ∩ U x ∧
        Metric.closedBall (chartTransition c d x.val) (t x) ⊆ (chartTransition c d).target ∩ V x ∧
        MapsTo (chartTransition c d) (Metric.closedBall x.val (s x))
          (Metric.ball (chartTransition c d x.val) (t x))) ∧
      (chartTransition c d).source ⊆ ⋃ x ∈ centers, Metric.ball x.val (s x / 2) := by
  classical
  let e := chartTransition c d
  choose s t h using fun x : e.source =>
    exists_chartTransition_ball_windows c d x.val x.property (U x) (V x) (hU x) (hV x)
  have hcover : e.source ⊆ ⋃ x : e.source, Metric.ball x.val (s x / 2) := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (h ⟨y, hy⟩).1)⟩
  have hL : IsLindelof e.source := IsLindelof.of_coe
  obtain ⟨centers, hCount, hSub⟩ := hL.elim_countable_subcover
    (fun x : e.source => Metric.ball x.val (s x / 2)) (fun _ => Metric.isOpen_ball) hcover
  exact ⟨s, t, centers, hCount, h, hSub⟩

end Burnett.Microlocal.OverlapWindows
