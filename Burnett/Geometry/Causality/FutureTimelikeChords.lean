import Burnett.Geometry.Causality.ChartTimeOrientation

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Straight segments with future timelike velocity in the actual chart. -/
def futureCoordinateChords {g : Field (M := M)} (o : TimeOrientation g) (c : M) :
    Set (CoordinateSpace × CoordinateSpace) :=
  {z | ∀ t ∈ Icc (0 : ℝ) 1,
    (AffineMap.lineMap z.1 z.2 t, z.2 - z.1) ∈ futureChartVelocities o c}

theorem isOpen_futureCoordinateChords {g : Field (M := M)} (hg : IsSmooth g)
    (o : TimeOrientation g) (c : M) : IsOpen (futureCoordinateChords o c) := by
  let F (w : ℝ × (CoordinateSpace × CoordinateSpace)) : CoordinateSpace × CoordinateSpace :=
    (AffineMap.lineMap w.2.1 w.2.2 w.1, w.2.2 - w.2.1)
  have hF : Continuous F := by
    change Continuous (fun w : ℝ × (CoordinateSpace × CoordinateSpace) =>
      (AffineMap.lineMap w.2.1 w.2.2 w.1, w.2.2 - w.2.1))
    simp only [AffineMap.lineMap_apply_module]
    fun_prop
  let Q := F ⁻¹' futureChartVelocities o c
  have hQ : IsOpen Q := (isOpen_futureChartVelocities hg o c).preimage hF
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  have hUniform : Q ∈ 𝓝ˢ (Icc (0 : ℝ) 1) ×ˢ 𝓝 z := by
    apply isCompact_Icc.mem_nhdsSet_prod_of_forall
    intro t ht
    rw [← nhds_prod_eq]
    exact hQ.mem_nhds (hz t ht)
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_prod_iff.mp hUniform
  apply mem_of_superset hV
  intro z' hz' t ht
  have htU : t ∈ U := mem_of_mem_nhds (mem_nhdsSet_iff_forall.mp hU t ht)
  exact hUV (show (t, z') ∈ U ×ˢ V from ⟨htU, hz'⟩)

/-- The starting and ending points of a straight future timelike segment
in some actual preferred chart. -/
def FutureTimelikeChartChord {g : Field (M := M)} (o : TimeOrientation g) (a b : M) : Prop :=
  ∃ c : M, let e := chartAt CoordinateSpace c
    a ∈ e.source ∧ b ∈ e.source ∧ (e a, e b) ∈ futureCoordinateChords o c

theorem isOpen_futureTimelikeChord {g : Field (M := M)} (hg : IsSmooth g)
    (o : TimeOrientation g) : IsOpen {p : M × M | FutureTimelikeChartChord o p.1 p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  rintro ⟨a, b⟩ ⟨c, ha, hb, hab⟩
  let e := chartAt CoordinateSpace c
  have hE : ContinuousAt (fun p : M × M => (e p.1, e p.2)) (a, b) :=
    (ContinuousAt.comp' (f := Prod.fst) (e.continuousAt ha) continuous_fst.continuousAt).prodMk
      (ContinuousAt.comp' (f := Prod.snd) (e.continuousAt hb) continuous_snd.continuousAt)
  have hsource : e.source ×ˢ e.source ∈ 𝓝 (a, b) :=
    (e.open_source.prod e.open_source).mem_nhds ⟨ha, hb⟩
  have hcoords := hE.preimage_mem_nhds ((isOpen_futureCoordinateChords hg o c).mem_nhds hab)
  filter_upwards [hsource, hcoords] with p hp hpc
  exact ⟨c, hp.1, hp.2, hpc⟩

/-- Concatenations of future timelike preferred-chart chords. -/
def chartChronology {g : Field (M := M)} (o : TimeOrientation g) : Set (M × M) :=
  {p | Relation.TransGen (FutureTimelikeChartChord o) p.1 p.2}

theorem isOpen_chartChronology {g : Field (M := M)} (hg : IsSmooth g)
    (o : TimeOrientation g) : IsOpen (chartChronology o) := by
  have hStep := isOpen_futureTimelikeChord hg o
  have hOpen {a b : M} (h : Relation.TransGen (FutureTimelikeChartChord o) a b) :
      chartChronology o ∈ 𝓝 (a, b) := by
    induction h with
    | single hab =>
        apply mem_of_superset (hStep.mem_nhds (show (a, _) ∈ _ from hab))
        exact fun _ hp => Relation.TransGen.single hp
    | @tail b c _ hbc ih =>
        obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.mp ih
        obtain ⟨W, hW, Z, hZ, hWZ⟩ := mem_nhds_prod_iff.mp (hStep.mem_nhds (show (b, c) ∈ _ from hbc))
        apply mem_nhds_prod_iff.mpr
        refine ⟨U, hU, Z, hZ, ?_⟩
        intro q hq
        have hqb : (q.1, b) ∈ chartChronology o := hUV ⟨hq.1, mem_of_mem_nhds hV⟩
        have hbq : FutureTimelikeChartChord o b q.2 :=
          hWZ (show (b, q.2) ∈ W ×ˢ Z from ⟨mem_of_mem_nhds hW, hq.2⟩)
        exact Relation.TransGen.tail hqb hbq
  exact isOpen_iff_mem_nhds.mpr fun p hp => hOpen hp

end Burnett.Geometry.FiniteCausalVolume
