import Burnett.Geometry.Causality.IntrinsicPiecewiseCausalEquivalence
import Burnett.Geometry.Causality.CausalVolumeTimeOnPaths

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section
namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.CotangentHamiltonCauchySlice

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The strong causality neighborhood condition in terms of causal endpoints.
If both endpoints are sufficiently near a point, every intermediate point
on a connecting causal path lies in the prescribed neighborhood. -/
def LocallyNoCausalReturn (J : Set (M × M)) : Prop :=
  ∀ x : M, ∀ U ∈ 𝓝 x, ∃ W ∈ 𝓝 x, ∀ ⦃a z b : M⦄,
    a ∈ W → b ∈ W → (a, z) ∈ J → (z, b) ∈ J → z ∈ U

/-- Global hyperbolicity stated using intrinsic piecewise `C¹` causal endpoints,
compact diamonds, and strong causality. -/
def IntrinsicPiecewiseGlobalHyperbolicity {g : Field (M := M)} (o : TimeOrientation g) : Prop :=
  (∀ a b : M, IsCompact {z : M | (a, z) ∈ intrinsicPiecewiseCausalRelation o ∧
    (z, b) ∈ intrinsicPiecewiseCausalRelation o}) ∧
  LocallyNoCausalReturn (intrinsicPiecewiseCausalRelation o)

/-- Strong causality supplies an open, causally convex neighborhood of every
point inside each prescribed neighborhood. -/
theorem exists_open_chartCausallyConvex_nhds_of_locallyNoCausalReturn {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g)
    (hStrong : LocallyNoCausalReturn (chartCausalRelation o)) (x : M) {U : Set M} (hU : U ∈ 𝓝 x) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ ⦃p z q : M⦄,
      p ∈ V → q ∈ V → (p, z) ∈ chartCausalRelation o → (z, q) ∈ chartCausalRelation o → z ∈ V := by
  obtain ⟨W, hW, hReturn⟩ := hStrong x U hU
  obtain ⟨a, b, ha, hb, hax, hxb⟩ := exists_past_future_chords_mem_nhds hg o x hW
  let V := {z : M | (a, z) ∈ chartChronology o ∧ (z, b) ∈ chartChronology o}
  have hI := isOpen_chartChronology hg o
  have hOpen : IsOpen V :=
    (hI.preimage (continuous_const.prodMk continuous_id)).inter
      (hI.preimage (continuous_id.prodMk continuous_const))
  have hxV : x ∈ V := ⟨Relation.TransGen.single hax, Relation.TransGen.single hxb⟩
  have hIJ := chartChronology_subset_chartCausalRelation o
  refine ⟨V, hOpen, hxV, fun z hz => hReturn ha hb (hIJ hz.1) (hIJ hz.2), ?_⟩
  intro p z q hp hq hpz hzq
  exact ⟨(chartCausalRelation_chronological_inclusions hg hL o hpz).1 hp.1,
    (chartCausalRelation_chronological_inclusions hg hL o hzq).2 hq.2⟩

private theorem no_timelike_loop_of_locallyNoCausalReturn [T2Space M] {g : Field (M := M)}
    (o : TimeOrientation g) (hStrong : LocallyNoCausalReturn (chartCausalRelation o))
    (p : M) : (p, p) ∉ chartChronology o := by
  have hAntisymm {x y : M} (hxy : (x, y) ∈ chartCausalRelation o) (hyx : (y, x) ∈ chartCausalRelation o) : x = y := by
    by_contra hne
    have hx : x ∈ ({y}ᶜ : Set M) := hne
    obtain ⟨W, hW, hReturn⟩ := hStrong x _ (isClosed_singleton.isOpen_compl.mem_nhds hx)
    have hxW := mem_of_mem_nhds hW
    have hy : y ∈ ({y}ᶜ : Set M) := hReturn hxW hxW hxy hyx
    exact hy (by simp)
  have hFirst {a b : M} (h : (a, b) ∈ chartChronology o) :
      ∃ z, FutureTimelikeChartChord o a z ∧ (z, b) ∈ chartCausalRelation o := by
    change Relation.TransGen (FutureTimelikeChartChord o) a b at h
    induction h with
    | single h => exact ⟨_, h, Relation.ReflTransGen.refl⟩
    | tail _ h ih =>
        obtain ⟨z, haz, hz⟩ := ih
        exact ⟨z, haz, chartCausalRelation_transitive o hz
          (chartChronology_subset_chartCausalRelation o (Relation.TransGen.single h))⟩
  intro h
  obtain ⟨z, hpz, hzp⟩ := hFirst h
  have hEqual : p = z := hAntisymm (chartChronology_subset_chartCausalRelation o (Relation.TransGen.single hpz)) hzp
  subst z
  obtain ⟨c, _, _, hChord⟩ := hpz
  have hNeg := (hChord 0 (left_mem_Icc.mpr zero_le_one)).2.1
  simp at hNeg

/-- The chart definition agrees with compact causal diamonds and the
strong causality neighborhood condition for genuine intrinsic piecewise
`C¹` causal curves. -/
theorem chartGlobalHyperbolicity_iff_intrinsicPiecewise [T2Space M] {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g) :
    ChartGlobalHyperbolicity o ↔ IntrinsicPiecewiseGlobalHyperbolicity o := by
  have hJ := chartCausalRelation_eq_intrinsicPiecewiseCausalRelation hg hL o
  constructor
  · intro hGH
    refine ⟨by simpa only [hJ] using hGH.compactDiamonds, ?_⟩
    intro x U hU
    obtain ⟨V, hV, hVU, hC⟩ := hGH.causalConvexNeighborhoods x U hU
    refine ⟨V, hV, ?_⟩
    intro a z b ha hb haz hzb
    exact hVU (hC ha hb (by rwa [hJ]) (by rwa [hJ]))
  · intro hGH
    have hStrong : LocallyNoCausalReturn (chartCausalRelation o) := by rw [hJ]; exact hGH.2
    refine ⟨no_timelike_loop_of_locallyNoCausalReturn o hStrong,
      by simpa only [hJ] using hGH.1, ?_⟩
    intro x U hU
    obtain ⟨V, hV, hxV, hVU, hC⟩ := exists_open_chartCausallyConvex_nhds_of_locallyNoCausalReturn hg hL o hStrong x hU
    exact ⟨V, hV.mem_nhds hxV, hVU, hC⟩

end Burnett.Geometry.FiniteCausalVolume
