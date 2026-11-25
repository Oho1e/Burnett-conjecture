import Burnett.Geometry.Causality.ChartChronologicalSteps
import Burnett.Geometry.Causality.ChronologicalVolume

set_option autoImplicit false
set_option maxHeartbeats 3300000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter MeasureTheory
open scoped ENNReal ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Every neighborhood contains both a future and a past endpoint of a
straight timelike segment from the center in its actual chart. -/
theorem exists_past_future_chords_mem_nhds {g : Field (M := M)} (hg : IsSmooth g)
    (o : TimeOrientation g) (p : M) {N : Set M} (hN : N ∈ 𝓝 p) :
    ∃ a b : M, a ∈ N ∧ b ∈ N ∧ FutureTimelikeChartChord o a p ∧ FutureTimelikeChartChord o p b := by
  let e := chartAt CoordinateSpace p
  let y := e p
  let v := ChartVectorField.coordinateVector o.vector p y
  have hp : p ∈ e.source := mem_chart_source CoordinateSpace p
  have hy : y ∈ e.target := e.mapsTo hp
  have hv : coordinateBilinear g p y v v < 0 := by
    change g (e.symm y) (tangentFrame p (e.symm y) v) (tangentFrame p (e.symm y) v) < 0
    rw [show tangentFrame p (e.symm y) v = o.vector (e.symm y) from
      ChartVectorField.tangentFrame_coordinateVector o.vector p hy]
    exact o.timelike _
  let P := {z : CoordinateSpace | (z, v) ∈ futureChartVelocities o p}
  have hP : IsOpen P := (isOpen_futureChartVelocities hg o p).preimage
    (continuous_id.prodMk continuous_const)
  have hN' : e.symm ⁻¹' N ∈ 𝓝 y := by
    have hE : ContinuousAt e.symm y := e.symm.continuousAt hy
    apply hE.preimage_mem_nhds
    rwa [e.left_inv hp]
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (hP.mem_nhds (show y ∈ P from ⟨hy, hv, hv⟩)) hN')
  let U := Metric.ball y r
  have hB : U ⊆ P := hBall.trans inter_subset_left
  have hyU : y ∈ U := Metric.mem_ball_self hr
  let plus (s : ℝ) : CoordinateSpace := y + s • v
  let minus (s : ℝ) : CoordinateSpace := y - s • v
  have hplus : Continuous plus := by dsimp only [plus]; fun_prop
  have hminus : Continuous minus := by dsimp only [minus]; fun_prop
  have hone : plus ⁻¹' U ∈ 𝓝 (0 : ℝ) := hplus.continuousAt.preimage_mem_nhds
    (Metric.isOpen_ball.mem_nhds (show plus 0 ∈ U by simpa [plus] using hyU))
  have htwo : minus ⁻¹' U ∈ 𝓝 (0 : ℝ) := hminus.continuousAt.preimage_mem_nhds
    (Metric.isOpen_ball.mem_nhds (show minus 0 ∈ U by simpa [minus] using hyU))
  obtain ⟨s, hs, hloc⟩ := Metric.mem_nhds_iff.mp (inter_mem hone htwo)
  let δ := s / 2
  have hδ : 0 < δ := half_pos hs
  have hw : δ ∈ Metric.ball (0 : ℝ) s := by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hδ]
    exact half_lt_self hs
  have hUp : plus δ ∈ U := (hloc hw).1
  have hUm : minus δ ∈ U := (hloc hw).2
  let a := e.symm (minus δ)
  let b := e.symm (plus δ)
  have hta : minus δ ∈ e.target := (hB hUm).1
  have htb : plus δ ∈ e.target := (hB hUp).1
  have hva : y - minus δ = δ • v := by dsimp [minus]; abel
  have hvb : plus δ - y = δ • v := by dsimp [plus]; abel
  refine ⟨a, b, (hBall hUm).2, (hBall hUp).2, ⟨p, e.symm_mapsTo hta, hp, ?_⟩, p, hp, e.symm_mapsTo htb, ?_⟩
  · intro t ht
    change (AffineMap.lineMap (e a) y t, y - e a) ∈ futureChartVelocities o p
    rw [show e a = minus δ from e.right_inv hta, hva]
    have hseg : AffineMap.lineMap (minus δ) y t ∈ U := by
      apply (convex_ball y r).segment_subset hUm hyU
      rw [segment_eq_image_lineMap]
      exact mem_image_of_mem _ ht
    exact futureChartVelocity_smul o p (hB hseg) hδ
  · intro t ht
    change (AffineMap.lineMap y (e b) t, e b - y) ∈ futureChartVelocities o p
    rw [show e b = plus δ from e.right_inv htb, hvb]
    have hseg : AffineMap.lineMap y (plus δ) t ∈ U := by
      apply (convex_ball y r).segment_subset hyU hUp
      rw [segment_eq_image_lineMap]
      exact mem_image_of_mem _ ht
    exact futureChartVelocity_smul o p (hB hseg) hδ

theorem exists_past_future_chords {g : Field (M := M)} (hg : IsSmooth g)
    (o : TimeOrientation g) (p : M) :
    ∃ a b : M, FutureTimelikeChartChord o a p ∧ FutureTimelikeChartChord o p b := by
  obtain ⟨a, b, _, _, ha, hb⟩ := exists_past_future_chords_mem_nhds hg o p univ_mem
  exact ⟨a, b, ha, hb⟩

variable [SecondCountableTopology M] [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- The actual oriented chart chronology has continuous logarithmic volume
time under the indicated closed-relation and no-loop conditions. The openness,
timelike chord and intermediate-point inputs are consequences of the metric. -/
theorem exists_logarithmic_volume_time_for_chartChronology {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g)
    {J : Set (M × M)} (hJ : IsClosed J) (hIJ : chartChronology o ⊆ J)
    (hNoLoop : ∀ a, (a, a) ∉ chartChronology o)
    (hPast : ∀ p, sectionAt J p ⊆ closure (sectionAt (chartChronology o) p))
    (hFuture : ∀ p, sectionAt (Prod.swap ⁻¹' J) p ⊆
      closure (sectionAt (Prod.swap ⁻¹' chartChronology o) p)) :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure ∧
      ManifoldVolume.geometricMeasure g ≪ μ ∧ μ ≪ ManifoldVolume.geometricMeasure g ∧
      let T := fun p => Real.log (μ (sectionAt (chartChronology o) p)).toReal -
        Real.log (μ (sectionAt (Prod.swap ⁻¹' chartChronology o) p)).toReal
      Continuous T ∧ ∀ {a b : M}, (a, b) ∈ chartChronology o → T a < T b := by
  apply exists_logarithmic_volume_time g hg hL (isOpen_chartChronology hg o) hJ hIJ
    (fun hab hbc => Relation.TransGen.trans hab hbc) hNoLoop ?_ (exists_middle_chartChronology o) ?_ ?_
    hPast hFuture
  · intro a b h
    exact (futureChord_or_reverse_of_timelike_chart_chord hg hL o h).imp
      Relation.TransGen.single Relation.TransGen.single
  · intro p
    obtain ⟨a, _, ha, _⟩ := exists_past_future_chords hg o p
    exact ⟨a, Relation.TransGen.single ha⟩
  · intro p
    obtain ⟨_, b, _, hb⟩ := exists_past_future_chords hg o p
    exact ⟨b, Relation.TransGen.single hb⟩

end Burnett.Geometry.FiniteCausalVolume
