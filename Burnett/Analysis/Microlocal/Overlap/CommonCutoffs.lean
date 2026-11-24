import Burnett.Analysis.Microlocal.Overlap.Localization
import Burnett.Analysis.LocalWeakDerivative
import Burnett.Geometry.FlatRigidity.WeakCurvature

/-!
# Common local cutoffs inside two preferred-chart cutoffs

A point in the interiors of both coordinate windows, where both original
cutoffs are nonzero, has nested coordinate balls and a single transported
cutoff. It factors through each original cutoff by a real smooth compactly
supported function. Both divisions are justified on the corresponding open
nonzero set. The inner source balls of a countable collection cover all such points.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapWindows

open Set Filter
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.OverlapGradient (exists_transportOverlapCutoff)
open Burnett.X02.SobolevTestJet (D test_smooth test_compactSupport)
open Burnett.Analysis.LocalWeakDerivative (contDiff_test_mul_local)
open scoped ContDiff Manifold Topology

private theorem isOpen_test_nonzero (f : D) :
    IsOpen (Function.support (f : CoordinateSpace → ℝ)) :=
  (isClosed_eq (test_smooth f).continuous continuous_const).isOpen_compl

/-- Divide a compactly supported test by a smooth test on its open nonzero set.
The resulting global factor is zero off the test's support. -/
theorem exists_testFactor_of_tsupport_subset_nonzero (f g : D)
    (hg : tsupport (g : CoordinateSpace → ℝ) ⊆ Function.support (f : CoordinateSpace → ℝ)) :
    ∃ a : D, tsupport (a : CoordinateSpace → ℝ) ⊆ tsupport (g : CoordinateSpace → ℝ) ∧
      ∀ x : CoordinateSpace, (g : CoordinateSpace → ℝ) x =
        (a : CoordinateSpace → ℝ) x * (f : CoordinateSpace → ℝ) x := by
  have hq : ContDiffOn ℝ ∞ (fun x => ((f : CoordinateSpace → ℝ) x)⁻¹)
      (Function.support (f : CoordinateSpace → ℝ)) :=
    (test_smooth f).contDiffOn.inv (fun _ hx => hx)
  let a : D := ⟨fun x => (g : CoordinateSpace → ℝ) x * ((f : CoordinateSpace → ℝ) x)⁻¹,
    contDiff_test_mul_local (isOpen_test_nonzero f) (test_smooth g) hg hq,
    (test_compactSupport g).mul_right⟩
  refine ⟨a, tsupport_mul_subset_left, ?_⟩
  intro x
  change (g : CoordinateSpace → ℝ) x =
    ((g : CoordinateSpace → ℝ) x * ((f : CoordinateSpace → ℝ) x)⁻¹) * (f : CoordinateSpace → ℝ) x
  by_cases hx : x ∈ Function.support (f : CoordinateSpace → ℝ)
  · rw [mul_assoc, inv_mul_cancel₀ hx, mul_one]
  · have hz : (g : CoordinateSpace → ℝ) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun h => hx (hg h))
    rw [hz, zero_mul, zero_mul]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- Source coordinates where both original charts admit a smaller common localization. -/
def nonzeroCutoffOverlap (c d : M) (U V : Set CoordinateSpace) (f g : D) : Set CoordinateSpace :=
  let e := chartTransition c d
  (e.source ∩ e ⁻¹' (interior V ∩ Function.support (g : CoordinateSpace → ℝ))) ∩
    (interior U ∩ Function.support (f : CoordinateSpace → ℝ))

theorem isOpen_nonzeroCutoffOverlap (c d : M) (U V : Set CoordinateSpace) (f g : D) :
    IsOpen (nonzeroCutoffOverlap c d U V f g) :=
  ((chartTransition c d).isOpen_inter_preimage (isOpen_interior.inter (isOpen_test_nonzero g))).inter
    (isOpen_interior.inter (isOpen_test_nonzero f))

/-- One common localization of the actual preferred-chart overlap. The original
tests are `f` in the source chart and `g` in the target chart. -/
structure CommonCutoffPatch (c d : M) (U V : Set CoordinateSpace) (f g : D) (x : CoordinateSpace) where
  sourceRadius : ℝ
  targetRadius : ℝ
  sourceRadius_pos : 0 < sourceRadius
  targetRadius_pos : 0 < targetRadius
  sourceWindow : Metric.closedBall x sourceRadius ⊆ (chartTransition c d).source ∩
    (interior U ∩ Function.support (f : CoordinateSpace → ℝ))
  targetWindow : Metric.closedBall (chartTransition c d x) targetRadius ⊆ (chartTransition c d).target ∩
    (interior V ∩ Function.support (g : CoordinateSpace → ℝ))
  mapsTo_targetBall : MapsTo (chartTransition c d) (Metric.closedBall x sourceRadius)
    (Metric.ball (chartTransition c d x) targetRadius)
  sourceCutoff : D
  targetCutoff : D
  sourceFactor : D
  targetFactor : D
  sourceCutoff_support : tsupport (sourceCutoff : CoordinateSpace → ℝ) ⊆ Metric.ball x sourceRadius
  targetCutoff_support_image : tsupport (targetCutoff : CoordinateSpace → ℝ) ⊆
    chartTransition c d '' tsupport (sourceCutoff : CoordinateSpace → ℝ)
  sourceCutoff_one : ∀ z ∈ Metric.closedBall x (sourceRadius / 2), (sourceCutoff : CoordinateSpace → ℝ) z = 1
  cutoff_transport : ∀ z ∈ (chartTransition c d).source,
    (targetCutoff : CoordinateSpace → ℝ) (chartTransition c d z) = (sourceCutoff : CoordinateSpace → ℝ) z
  sourceFactor_support : tsupport (sourceFactor : CoordinateSpace → ℝ) ⊆
    tsupport (sourceCutoff : CoordinateSpace → ℝ)
  targetFactor_support : tsupport (targetFactor : CoordinateSpace → ℝ) ⊆
    tsupport (targetCutoff : CoordinateSpace → ℝ)
  sourceCutoff_eq_mul : ∀ z, (sourceCutoff : CoordinateSpace → ℝ) z =
    (sourceFactor : CoordinateSpace → ℝ) z * (f : CoordinateSpace → ℝ) z
  targetCutoff_eq_mul : ∀ z, (targetCutoff : CoordinateSpace → ℝ) z =
    (targetFactor : CoordinateSpace → ℝ) z * (g : CoordinateSpace → ℝ) z

namespace CommonCutoffPatch

variable {c d : M} {U V : Set CoordinateSpace} {f g : D} {x : CoordinateSpace}

theorem targetCutoff_support (p : CommonCutoffPatch c d U V f g x) :
    tsupport (p.targetCutoff : CoordinateSpace → ℝ) ⊆
      Metric.ball (chartTransition c d x) p.targetRadius := by
  apply p.targetCutoff_support_image.trans
  rintro y ⟨z, hz, rfl⟩
  exact p.mapsTo_targetBall (Metric.ball_subset_closedBall (p.sourceCutoff_support hz))

theorem targetCutoff_one_on_image (p : CommonCutoffPatch c d U V f g x) :
    ∀ y ∈ chartTransition c d '' Metric.closedBall x (p.sourceRadius / 2),
      (p.targetCutoff : CoordinateSpace → ℝ) y = 1 := by
  rintro y ⟨z, hz, rfl⟩
  have hzs : z ∈ (chartTransition c d).source := by
    apply (p.sourceWindow (Metric.closedBall_subset_closedBall _ hz)).1
    linarith [p.sourceRadius_pos]
  exact (p.cutoff_transport z hzs).trans (p.sourceCutoff_one z hz)

theorem sourceWindow_subset_nonzeroCutoffOverlap (p : CommonCutoffPatch c d U V f g x) :
    Metric.closedBall x p.sourceRadius ⊆ nonzeroCutoffOverlap c d U V f g := by
  intro z hz
  exact ⟨⟨(p.sourceWindow hz).1,
    (p.targetWindow (Metric.ball_subset_closedBall (p.mapsTo_targetBall hz))).2⟩, (p.sourceWindow hz).2⟩

end CommonCutoffPatch

variable [IsManifold Model ∞ M]

/-- A source cutoff with a half-radius plateau and its actual transported
target cutoff, both factored through the given local cutoffs. -/
theorem exists_commonCutoffPatch (c d : M) (U V : Set CoordinateSpace) (f g : D)
    (x : CoordinateSpace) (hx : x ∈ (chartTransition c d).source)
    (hxU : x ∈ interior U) (hyV : chartTransition c d x ∈ interior V)
    (hf : (f : CoordinateSpace → ℝ) x ≠ 0)
    (hg : (g : CoordinateSpace → ℝ) (chartTransition c d x) ≠ 0) :
    Nonempty (CommonCutoffPatch c d U V f g x) := by
  let e := chartTransition c d
  have hU := (isOpen_interior.inter (isOpen_test_nonzero f)).mem_nhds ⟨hxU, hf⟩
  have hV := (isOpen_interior.inter (isOpen_test_nonzero g)).mem_nhds ⟨hyV, hg⟩
  obtain ⟨s, t, hs, ht, hsWindow, htWindow, hMaps⟩ :=
    exists_chartTransition_ball_windows c d x hx _ _ hU hV
  have hInner : Metric.closedBall x (s / 2) ⊆ Metric.ball x s :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨_, _, _, hSub, χ, hχ, hχCompact, hχSub, _, hχOne⟩ :=
    Burnett.Geometry.FlatRigidity.exists_smooth_cutoff_on_compact_chart
      (isCompact_closedBall x (s / 2)) Metric.isOpen_ball hInner
  let χc : D := ⟨χ, hχ, hχCompact⟩
  have hχB : tsupport χ ⊆ Metric.ball x s := hχSub.trans hSub
  have hχS : tsupport χ ⊆ e.source := fun _ hz => (hsWindow (Metric.ball_subset_closedBall (hχB hz))).1
  obtain ⟨η, hηI, hTransport⟩ := exists_transportOverlapCutoff c d χc hχS
  have hηB : tsupport (η : CoordinateSpace → ℝ) ⊆ Metric.ball (e x) t := by
    apply hηI.trans
    rintro y ⟨z, hz, rfl⟩
    exact hMaps (Metric.ball_subset_closedBall (hχB hz))
  obtain ⟨a, ha, hFactorSource⟩ := exists_testFactor_of_tsupport_subset_nonzero f χc
    (fun _ hz => (hsWindow (Metric.ball_subset_closedBall (hχB hz))).2.2)
  obtain ⟨b, hb, hFactorTarget⟩ := exists_testFactor_of_tsupport_subset_nonzero g η
    (fun _ hz => (htWindow (Metric.ball_subset_closedBall (hηB hz))).2.2)
  exact ⟨⟨s, t, hs, ht, hsWindow, htWindow, hMaps, χc, η, a, b, hχB, hηI,
    hχOne, hTransport, ha, hb, hFactorSource, hFactorTarget⟩⟩

/-- A countable family of these patches covers exactly the source points that
lie in both window interiors and where both original cutoffs are nonzero. -/
theorem exists_countable_commonCutoffPatches (c d : M) (U V : Set CoordinateSpace) (f g : D) :
    ∃ (p : ∀ x : nonzeroCutoffOverlap c d U V f g, CommonCutoffPatch c d U V f g x.val)
      (centers : Set (nonzeroCutoffOverlap c d U V f g)),
      centers.Countable ∧
      nonzeroCutoffOverlap c d U V f g = ⋃ x ∈ centers, Metric.ball x.val ((p x).sourceRadius / 2) := by
  classical
  let W := nonzeroCutoffOverlap c d U V f g
  let p (x : W) := Classical.choice (exists_commonCutoffPatch c d U V f g x.val
    x.property.1.1 x.property.2.1 x.property.1.2.1 x.property.2.2 x.property.1.2.2)
  have hCover : W ⊆ ⋃ x : W, Metric.ball x.val ((p x).sourceRadius / 2) := by
    intro y hy
    exact mem_iUnion.mpr ⟨⟨y, hy⟩, Metric.mem_ball_self (half_pos (p ⟨y, hy⟩).sourceRadius_pos)⟩
  obtain ⟨centers, hCountable, hSubcover⟩ := (IsLindelof.of_coe : IsLindelof W).elim_countable_subcover
    (fun x : W => Metric.ball x.val ((p x).sourceRadius / 2)) (fun _ => Metric.isOpen_ball) hCover
  refine ⟨p, centers, hCountable, Subset.antisymm hSubcover ?_⟩
  refine iUnion₂_subset fun x _ => ?_
  have hHalf : (p x).sourceRadius / 2 ≤ (p x).sourceRadius := by linarith [(p x).sourceRadius_pos]
  exact Metric.ball_subset_closedBall.trans ((Metric.closedBall_subset_closedBall hHalf).trans
    (p x).sourceWindow_subset_nonzeroCutoffOverlap)

end Burnett.Microlocal.OverlapWindows
