import Burnett.Geometry.Causality.FutureTimelikeChords

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem futureChord_or_reverse_of_timelike_chart_chord {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g)
    {a b : M} (h : HasTimelikeChartChord g a b) :
    FutureTimelikeChartChord o a b ∨ FutureTimelikeChartChord o b a := by
  obtain ⟨c, ha, hb, hline⟩ := h
  let e := chartAt CoordinateSpace c
  let y : ℝ → CoordinateSpace := AffineMap.lineMap (e a) (e b)
  let v := e b - e a
  let n := ChartVectorField.coordinateVector o.vector c
  let f (t : ℝ) := coordinateBilinear g c (y t) (n (y t)) v
  have hAt (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : ContinuousAt f t := by
    have hy : ContinuousAt y t := by
      change ContinuousAt (fun s => AffineMap.lineMap (e a) (e b) s) t
      simp only [AffineMap.lineMap_apply_module]
      fun_prop
    have hyn : y t ∈ e.target := (hline t ht).1
    have hn := (ChartVectorField.contDiffOn_coordinateVector o.vector o.smooth c).continuousOn
      |>.continuousAt (e.open_target.mem_nhds hyn)
    exact continuousAt_actual_chart_pairing g hg c t y (n ∘ y) (fun _ => v) hy
      (ContinuousAt.comp (f := y) hn hy) continuousAt_const hyn
  have hcon : ContinuousOn f (Icc 0 1) := fun t ht => (hAt t ht).continuousWithinAt
  have hne (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t ≠ 0 :=
    chart_time_pairing_ne_zero hL o c (hline t ht).1 (hline t ht).2
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := left_mem_Icc.mpr zero_le_one
  rcases lt_or_gt_of_ne (hne 0 h0) with hneg₀ | hpos₀
  · left
    refine ⟨c, ha, hb, fun t ht => ⟨(hline t ht).1, (hline t ht).2, ?_⟩⟩
    change f t < 0
    by_contra! htneg
    have hI : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) 1 := fun _ hs => ⟨hs.1, hs.2.trans ht.2⟩
    obtain ⟨s, hs, hzero⟩ := intermediate_value_Icc ht.1 (hcon.mono hI) ⟨hneg₀.le, htneg⟩
    exact hne s (hI hs) hzero
  · right
    refine ⟨c, hb, ha, fun t ht => ?_⟩
    have hs : 1 - t ∈ Icc (0 : ℝ) 1 := ⟨sub_nonneg.mpr ht.2, sub_le_self _ ht.1⟩
    have hsign : 0 < f (1 - t) := by
      by_contra! htn
      have hI : Icc (0 : ℝ) (1 - t) ⊆ Icc (0 : ℝ) 1 := fun _ hz => ⟨hz.1, hz.2.trans hs.2⟩
      obtain ⟨s, hs', hzero⟩ := intermediate_value_Icc' hs.1 (hcon.mono hI) ⟨htn, hpos₀.le⟩
      exact hne s (hI hs') hzero
    have hY := (hline (1 - t) hs).1
    have hv := (hline (1 - t) hs).2
    change (AffineMap.lineMap (e b) (e a) t, e a - e b) ∈ futureChartVelocities o c
    have hD : e a - e b = -(e b - e a) := (neg_sub (e b) (e a)).symm
    rw [← AffineMap.lineMap_apply_one_sub, hD]
    refine ⟨hY, ?_, ?_⟩
    · simpa only [map_neg, LinearMap.neg_apply, neg_neg] using hv
    · simpa only [map_neg] using neg_neg_of_pos hsign

theorem futureChartVelocity_smul {g : Field (M := M)} (o : TimeOrientation g) (c : M)
    {y v : CoordinateSpace} (h : (y, v) ∈ futureChartVelocities o c) {s : ℝ} (hs : 0 < s) :
    (y, s • v) ∈ futureChartVelocities o c := by
  refine ⟨h.1, ?_, ?_⟩
  · simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hs (mul_neg_of_pos_of_neg hs h.2.1)
  · simp only [map_smul, smul_eq_mul]
    exact mul_neg_of_pos_of_neg hs h.2.2

/-- Splitting the actual affine parameter at one half keeps both segments
in the same chart with future timelike velocity. -/
theorem exists_middle_futureTimelikeChord {g : Field (M := M)} (o : TimeOrientation g)
    {a b : M} (h : FutureTimelikeChartChord o a b) :
    ∃ m, FutureTimelikeChartChord o a m ∧ FutureTimelikeChartChord o m b := by
  obtain ⟨c, ha, hb, hline⟩ := h
  let e := chartAt CoordinateSpace c
  let y := AffineMap.lineMap (e a) (e b) (1 / 2 : ℝ)
  let m := e.symm y
  have hy : y ∈ e.target := (hline (1 / 2) (by norm_num)).1
  have hm : m ∈ e.source := e.symm_mapsTo hy
  have hmy : e m = y := e.right_inv hy
  have hd₁ : y - e a = (1 / 2 : ℝ) • (e b - e a) :=
    AffineMap.lineMap_vsub_left (e a) (e b) (1 / 2 : ℝ)
  have hd₂ : e b - y = (1 / 2 : ℝ) • (e b - e a) := by
    have hHalf : (1 : ℝ) - 1 / 2 = 1 / 2 := by norm_num
    simpa only [hHalf] using AffineMap.right_vsub_lineMap (e a) (e b) (1 / 2 : ℝ)
  refine ⟨m, ⟨c, ha, hm, ?_⟩, c, hm, hb, ?_⟩
  · intro t ht
    have ht' : t * (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    change (AffineMap.lineMap (e a) (e m) t, e m - e a) ∈ futureChartVelocities o c
    rw [hmy, hd₁]
    dsimp only [y]
    rw [AffineMap.lineMap_lineMap_right]
    exact futureChartVelocity_smul o c (hline _ ht') (by norm_num)
  · intro t ht
    have ht' : 1 - (1 - t) * (1 - (1 / 2 : ℝ)) ∈ Icc (0 : ℝ) 1 :=
      ⟨by nlinarith [ht.1], by nlinarith [ht.2]⟩
    change (AffineMap.lineMap (e m) (e b) t, e b - e m) ∈ futureChartVelocities o c
    rw [hmy, hd₂]
    dsimp only [y]
    rw [AffineMap.lineMap_lineMap_left]
    exact futureChartVelocity_smul o c (hline _ ht') (by norm_num)

theorem exists_middle_chartChronology {g : Field (M := M)} (o : TimeOrientation g)
    {a b : M} (h : (a, b) ∈ chartChronology o) :
    ∃ m : M, (a, m) ∈ chartChronology o ∧ (m, b) ∈ chartChronology o := by
  change Relation.TransGen _ _ _ at h
  cases h with
  | single h =>
      obtain ⟨m, ha, hb⟩ := exists_middle_futureTimelikeChord o h
      exact ⟨m, Relation.TransGen.single ha, Relation.TransGen.single hb⟩
  | @tail m b h₁ h₂ => exact ⟨m, h₁, Relation.TransGen.single h₂⟩

end Burnett.Geometry.FiniteCausalVolume
