import Burnett.Geometry.Causality.ChartChronologicalNeighborhoods
import Mathlib.Topology.ClusterPt

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

/-- Compact diamonds give a closed causal order whenever the open chronology
approaches each point from the past and supplies a timelike future. -/
theorem isClosed_relation_of_compact_diamonds {M : Type*} [TopologicalSpace M] [T2Space M]
    {I J : Set (M × M)} (hI : IsOpen I) (hIJ : I ⊆ J)
    (hTrans : Transitive fun a b => (a, b) ∈ J)
    (hPast : ∀ x : M, x ∈ closure {a : M | (a, x) ∈ I})
    (hFuture : ∀ y : M, ∃ b : M, (y, b) ∈ I)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ J ∧ (z, b) ∈ J}) : IsClosed J := by
  apply closure_subset_iff_isClosed.mp
  rintro ⟨x, y⟩ hxy
  have hAY (a : M) (hax : (a, x) ∈ I) : (a, y) ∈ J := by
    obtain ⟨b, hyb⟩ := hFuture y
    let D : Set M := {z | (a, z) ∈ J ∧ (z, b) ∈ J}
    have hD : IsClosed D := (hDiam a b).isClosed
    have hy : y ∈ closure D := by
      apply mem_closure_iff_nhds.mpr
      intro V hV
      let W : Set (M × M) := (fun p : M × M => (a, p.1)) ⁻¹' I ∩
        (fun p : M × M => (p.2, b)) ⁻¹' I ∩ Prod.snd ⁻¹' V
      have hW : W ∈ 𝓝 (x, y) := inter_mem (inter_mem
        ((continuous_const.prodMk continuous_fst).continuousAt.preimage_mem_nhds (hI.mem_nhds hax))
        ((continuous_snd.prodMk continuous_const).continuousAt.preimage_mem_nhds (hI.mem_nhds hyb)))
        (continuous_snd.continuousAt.preimage_mem_nhds hV)
      obtain ⟨⟨u, v⟩, hNear, hJ⟩ := mem_closure_iff_nhds.mp hxy W hW
      exact ⟨v, hNear.2, hTrans (hIJ hNear.1.1) hJ, hIJ hNear.1.2⟩
    exact (hD.closure_eq ▸ hy).1
  obtain ⟨a, _, hax⟩ := mem_closure_iff_nhds.mp (hPast x) univ univ_mem
  let D : Set M := {z | (a, z) ∈ J ∧ (z, y) ∈ J}
  have hD : IsClosed D := (hDiam a y).isClosed
  have hx : x ∈ closure D := by
    apply mem_closure_iff_nhds.mpr
    intro V hV
    let W := V ∩ (fun z : M => (a, z)) ⁻¹' I
    have hW : W ∈ 𝓝 x := inter_mem hV
      ((continuous_const.prodMk continuous_id).continuousAt.preimage_mem_nhds (hI.mem_nhds hax))
    obtain ⟨z, hz, hzx⟩ := mem_closure_iff_nhds.mp (hPast x) W hW
    exact ⟨z, hz.1, hIJ hz.2, hAY z hzx⟩
  exact (hD.closure_eq ▸ hx).2

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M] [T2Space M]

theorem isClosed_causalRelation_of_compact_diamonds {g : Field (M := M)}
    (hg : IsSmooth g) (o : TimeOrientation g) {J : Set (M × M)}
    (hIJ : chartChronology o ⊆ J) (hTrans : Transitive fun a b => (a, b) ∈ J)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ J ∧ (z, b) ∈ J}) : IsClosed J := by
  apply isClosed_relation_of_compact_diamonds (isOpen_chartChronology hg o) hIJ hTrans ?_ ?_ hDiam
  · intro p
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨a, _, ha, _, hc, _⟩ := exists_past_future_chords_mem_nhds hg o p hV
    exact ⟨a, ha, Relation.TransGen.single hc⟩
  · intro p
    obtain ⟨_, b, _, hb⟩ := exists_past_future_chords hg o p
    exact ⟨b, Relation.TransGen.single hb⟩

end Burnett.Geometry.FiniteCausalVolume
