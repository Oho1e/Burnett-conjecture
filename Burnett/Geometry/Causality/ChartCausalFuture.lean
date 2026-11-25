import Burnett.Geometry.Causality.ChartCausalChronology

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

private theorem coordinateVector_neg (V : ChartVectorField.Field (M := M)) (c : M) {y : E}
    (hy : y ∈ (chartAt E c).target) :
    ChartVectorField.coordinateVector (fun x => -V x) c y = -ChartVectorField.coordinateVector V c y := by
  apply tangentFrame_injective c _ ((chartAt E c).symm_mapsTo hy)
  rw [map_neg, ChartVectorField.tangentFrame_coordinateVector _ c hy,
    ChartVectorField.tangentFrame_coordinateVector _ c hy]

def TimeOrientation.reverse {g : Field (M := M)} (o : TimeOrientation g) : TimeOrientation g where
  vector x := -o.vector x
  smooth := ChartVectorField.isSmooth_of_contDiffOn_coordinateVector _ (fun c =>
    (ChartVectorField.contDiffOn_coordinateVector _ o.smooth c).neg.congr (fun _ h => coordinateVector_neg _ c h))
  timelike x := by simpa only [map_neg, ContinuousLinearMap.neg_apply, neg_neg] using o.timelike x

theorem TimeOrientation.reverse_reverse {g : Field (M := M)} (o : TimeOrientation g) : o.reverse.reverse = o := by
  cases o with
  | mk v hS hT =>
    simp only [TimeOrientation.reverse, neg_neg]

private theorem reverse_futureChartVelocity {g : Field (M := M)} (o : TimeOrientation g) (c : M)
    {y v : E} (h : (y, v) ∈ futureChartVelocities o c) : (y, -v) ∈ futureChartVelocities o.reverse c := by
  refine ⟨h.1, ?_, ?_⟩
  · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using h.2.1
  · change coordinateBilinear g c y (ChartVectorField.coordinateVector (fun x => -o.vector x) c y) (-v) < 0
    rw [coordinateVector_neg o.vector c h.1]
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using h.2.2

private theorem reverse_futureTimelikeChord {g : Field (M := M)} (o : TimeOrientation g) {a b : M}
    (h : FutureTimelikeChartChord o a b) : FutureTimelikeChartChord o.reverse b a := by
  obtain ⟨c, ha, hb, hC⟩ := h
  let e := chartAt E c
  refine ⟨c, hb, ha, fun t ht => ?_⟩
  have hs : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
  have h := reverse_futureChartVelocity o c (hC (1 - t) hs)
  change (AffineMap.lineMap (e b) (e a) t, e a - e b) ∈ futureChartVelocities o.reverse c
  rw [← AffineMap.lineMap_apply_one_sub, show e a - e b = -(e b - e a) from (neg_sub _ _).symm]
  exact h

theorem reverse_chartChronology {g : Field (M := M)} (o : TimeOrientation g) {a b : M}
    (h : (a, b) ∈ chartChronology o) : (b, a) ∈ chartChronology o.reverse := by
  change Relation.TransGen _ a b at h
  induction h with
  | single h => exact Relation.TransGen.single (reverse_futureTimelikeChord o h)
  | tail h₁ h₂ ih => exact Relation.TransGen.trans (Relation.TransGen.single (reverse_futureTimelikeChord o h₂)) ih

theorem chartChronology_reverse_iff {g : Field (M := M)} (o : TimeOrientation g) {a b : M} :
    (a, b) ∈ chartChronology o.reverse ↔ (b, a) ∈ chartChronology o := by
  refine ⟨fun h => ?_, reverse_chartChronology o⟩
  simpa only [TimeOrientation.reverse_reverse] using reverse_chartChronology o.reverse h

/-- The corresponding chronological future inclusion follows by reversing
both the actual time orientation and the affine parameter. -/
theorem chartCausalWindow_future_subset {g : Field (M := M)} (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation g) (c : M) (x n : E) {r R a b V : ℝ} (hab : a < b) (hRad : r < R)
    (hTarget : Metric.closedBall x R ⊆ (chartAt E c).target)
    (hn : ∀ z ∈ Metric.closedBall x R, coordinateBilinear g c z n n < 0)
    (hnT : ∀ z ∈ Metric.closedBall x R,
      coordinateBilinear g c z n (ChartVectorField.coordinateVector o.vector c z) < 0)
    (y v : ℝ → E) (hV : 0 ≤ V)
    (hpath : ∀ t ∈ Icc a b, y t ∈ Metric.closedBall x r ∧ HasDerivAt y (v t) t ∧
      coordinateBilinear g c (y t) (v t) (v t) ≤ 0 ∧
      coordinateBilinear g c (y t) n (v t) ≤ 0 ∧ ‖v t‖ ≤ V) :
    sectionAt (Prod.swap ⁻¹' chartChronology o) ((chartAt E c).symm (y b)) ⊆
      sectionAt (Prod.swap ⁻¹' chartChronology o) ((chartAt E c).symm (y a)) := by
  let Y := fun t : ℝ => y (-t)
  let W := fun t : ℝ => -v (-t)
  have hn' (z : E) (hz : z ∈ Metric.closedBall x R) : coordinateBilinear g c z (-n) (-n) < 0 := by
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hn z hz
  have hnT' (z : E) (hz : z ∈ Metric.closedBall x R) :
      coordinateBilinear g c z (-n) (ChartVectorField.coordinateVector o.reverse.vector c z) < 0 := by
    change coordinateBilinear g c z (-n) (ChartVectorField.coordinateVector (fun p => -o.vector p) c z) < 0
    rw [coordinateVector_neg o.vector c (hTarget hz)]
    simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hnT z hz
  have hPath (t : ℝ) (ht : t ∈ Icc (-b) (-a)) : Y t ∈ Metric.closedBall x r ∧ HasDerivAt Y (W t) t ∧
      coordinateBilinear g c (Y t) (W t) (W t) ≤ 0 ∧
      coordinateBilinear g c (Y t) (-n) (W t) ≤ 0 ∧ ‖W t‖ ≤ V := by
    have ht' : -t ∈ Icc a b := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    obtain ⟨hy, hd, hv, hnv, hSize⟩ := hpath (-t) ht'
    refine ⟨hy, ?_, ?_, ?_, by simpa only [W, norm_neg] using hSize⟩
    · simpa only [Y, W, Function.comp_apply, neg_smul, one_smul] using hd.scomp t (hasDerivAt_id t).neg
    · simpa only [Y, W, map_neg, LinearMap.neg_apply, neg_neg] using hv
    · simpa only [Y, W, map_neg, LinearMap.neg_apply, neg_neg] using hnv
  have hIncl := chartCausalWindow_past_subset hg hL o.reverse c x (-n) (neg_lt_neg hab) hRad hTarget hn' hnT' Y W hV hPath
  intro q hq
  have hOld : (q, (chartAt E c).symm (Y (-b))) ∈ chartChronology o.reverse :=
    (chartChronology_reverse_iff o).mpr (by simpa only [Y, neg_neg] using hq)
  have hNew := (chartChronology_reverse_iff o).mp (hIncl hOld)
  simpa only [Y, neg_neg] using hNew

end Burnett.Geometry.FiniteCausalVolume
