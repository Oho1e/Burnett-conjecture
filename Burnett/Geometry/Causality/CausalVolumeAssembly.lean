import Burnett.Geometry.Causality.CausalVolumeStrict

set_option autoImplicit false
set_option maxHeartbeats 4400000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter MeasureTheory
open scoped ENNReal ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- On a spacetime with compact causal diamonds, causally convex local
neighborhoods and the chronological inclusions, the logarithmic volume
time is continuous and strictly increases on distinct causal endpoints. -/
theorem exists_continuous_strictCausal_volume_time {g : Field (M := M)}
    (hg : IsSmooth g) (hL : HasLorentzSignature g) (o : TimeOrientation g) {J : Set (M × M)}
    (hIJ : chartChronology o ⊆ J) (hTrans : Transitive fun a b => (a, b) ∈ J)
    (hNoLoop : ∀ a, (a, a) ∉ chartChronology o)
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ J ∧ (z, b) ∈ J})
    (hLoc : ∀ x : M, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → (a, z) ∈ J → (z, b) ∈ J → z ∈ V)
    (hPast : ∀ ⦃a b : M⦄, (a, b) ∈ J → sectionAt (chartChronology o) a ⊆ sectionAt (chartChronology o) b)
    (hFuture : ∀ ⦃a b : M⦄, (a, b) ∈ J → sectionAt (Prod.swap ⁻¹' chartChronology o) b ⊆
      sectionAt (Prod.swap ⁻¹' chartChronology o) a) :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure ∧
      ManifoldVolume.geometricMeasure g ≪ μ ∧ μ ≪ ManifoldVolume.geometricMeasure g ∧
      let T p := Real.log (μ (sectionAt (chartChronology o) p)).toReal -
        Real.log (μ (sectionAt (Prod.swap ⁻¹' chartChronology o) p)).toReal
      Continuous T ∧ ∀ ⦃a b : M⦄, (a, b) ∈ J → a ≠ b → T a < T b := by
  let I := chartChronology o
  have hJ := isClosed_causalRelation_of_compact_diamonds hg o hIJ hTrans hDiam
  have hAround (x : M) (V : Set M) (hV : V ∈ 𝓝 x) :
      ∃ a b : M, a ∈ V ∧ b ∈ V ∧ (a, x) ∈ I ∧ (x, b) ∈ I := by
    obtain ⟨a, b, ha, hb, hax, hxb⟩ := exists_past_future_chords_mem_nhds hg o x hV
    exact ⟨a, b, ha, hb, Relation.TransGen.single hax, Relation.TransGen.single hxb⟩
  have hPastClose (b : M) : sectionAt J b ⊆ closure (sectionAt I b) := by
    intro a hab
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨q, _, hq, _, hqa, _⟩ := hAround a V hV
    exact ⟨q, hq, hPast hab hqa⟩
  have hFutureClose (a : M) : sectionAt (Prod.swap ⁻¹' J) a ⊆
      closure (sectionAt (Prod.swap ⁻¹' I) a) := by
    intro b hab
    apply mem_closure_iff_nhds.mpr
    intro V hV
    obtain ⟨_, q, _, hq, _, hbq⟩ := hAround b V hV
    exact ⟨q, hq, hFuture hab hbq⟩
  obtain ⟨μ, hFinite, hPos, hvμ, hμv, hT, _⟩ := exists_logarithmic_volume_time_for_chartChronology
    hg hL o hJ hIJ hNoLoop hPastClose hFutureClose
  letI := hFinite
  letI := hPos
  refine ⟨μ, hFinite, hPos, hvμ, hμv, hT, fun a b hab hne => ?_⟩
  exact logarithmic_volume_time_strict_along_causal μ (isOpen_chartChronology hg o) hIJ
    (fun _ _ _ h h' => Relation.TransGen.trans h h') (by intro a b h; exact exists_middle_chartChronology o h) hAround hLoc
    hne (hPast hab) (hFuture hab)

end Burnett.Geometry.FiniteCausalVolume
