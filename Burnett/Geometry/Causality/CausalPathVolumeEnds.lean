import Burnett.Geometry.Causality.CausalChartRelation
import Burnett.Geometry.Causality.CausalCompactEnds
import Burnett.Geometry.Causality.VolumeTimeEnds

set_option autoImplicit false
set_option maxHeartbeats 6000000

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter MeasureTheory
open scoped ContDiff ENNReal Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [MeasurableSpace M]

private theorem isOpenPos_chartChronology_sections {g : Field (M := M)} (hg : IsSmooth g)
    (o : TimeOrientation g) (μ : Measure M) [μ.IsOpenPosMeasure] (x : M) :
    μ (sectionAt (chartChronology o) x) ≠ 0 ∧ μ (sectionAt (Prod.swap ⁻¹' chartChronology o) x) ≠ 0 := by
  obtain ⟨a, b, ha, hb⟩ := exists_past_future_chords hg o x
  have hI := isOpen_chartChronology hg o
  have hPast : IsOpen (sectionAt (chartChronology o) x) :=
    hI.preimage (continuous_id.prodMk continuous_const)
  have hFuture : IsOpen (sectionAt (Prod.swap ⁻¹' chartChronology o) x) :=
    hI.preimage (continuous_const.prodMk continuous_id)
  exact ⟨(hPast.measure_pos μ ⟨a, Relation.TransGen.single ha⟩).ne',
    (hFuture.measure_pos μ ⟨b, Relation.TransGen.single hb⟩).ne'⟩

variable [BorelSpace M]

/-- The logarithmic volume time diverges at both ends of a two-sided ordered
causal path without endpoint limits. Compact diamonds and local causal
convexity exclude common future or past endpoints. -/
theorem causal_path_logVolume_diverges {ι : Type*} [LinearOrder ι] [Nonempty ι]
    [IsCountablyGenerated (atTop : Filter ι)] [IsCountablyGenerated (atBot : Filter ι)]
    {g : Field (M := M)} (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (o : TimeOrientation g) (μ : Measure M) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hDiam : ∀ a b : M, IsCompact {z : M | (a, z) ∈ chartCausalRelation o ∧ (z, b) ∈ chartCausalRelation o})
    (hLoc : ∀ x : M, ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → (a, z) ∈ chartCausalRelation o → (z, b) ∈ chartCausalRelation o → z ∈ V)
    (γ : ι → M) (hOrd : ∀ {a b : ι}, a ≤ b → (γ a, γ b) ∈ chartCausalRelation o)
    (hPast : ∀ x : M, ¬ Tendsto γ atBot (𝓝 x)) (hFuture : ∀ x : M, ¬ Tendsto γ atTop (𝓝 x)) :
    let T p := Real.log (μ (sectionAt (chartChronology o) p)).toReal -
      Real.log (μ (sectionAt (Prod.swap ⁻¹' chartChronology o) p)).toReal
    Tendsto (T ∘ γ) atBot atBot ∧ Tendsto (T ∘ γ) atTop atTop := by
  intro T
  let R := fun a b : M => (a, b) ∈ chartCausalRelation o
  let P (t : ι) := sectionAt (chartChronology o) (γ t)
  let F (t : ι) := sectionAt (Prod.swap ⁻¹' chartChronology o) (γ t)
  have hP : Monotone P := fun _ _ h =>
    (chartCausalRelation_chronological_inclusions hg hL o (hOrd h)).1
  have hF : Antitone F := fun _ _ h =>
    (chartCausalRelation_chronological_inclusions hg hL o (hOrd h)).2
  have hBefore (t : ι) : μ (P t) ≠ 0 := (isOpenPos_chartChronology_sections hg o μ (γ t)).1
  have hAfter (t : ι) : μ (F t) ≠ 0 := (isOpenPos_chartChronology_sections hg o μ (γ t)).2
  have hI := isOpen_chartChronology hg o
  have hPmeas (t : ι) : MeasurableSet (P t) :=
    (hI.preimage (continuous_id.prodMk continuous_const)).measurableSet
  have hFmeas (t : ι) : MeasurableSet (F t) :=
    (hI.preimage (continuous_const.prodMk continuous_id)).measurableSet
  have hNoFuture : (⋂ i, {x : M | R (γ i) x}) = ∅ :=
    iInter_future_eq_empty_of_no_limit R γ (fun h => hOrd h) hLoc hDiam hFuture
  have hFempty : μ (⋂ i, F i) = 0 := by
    have hSub : (⋂ i, F i) ⊆ ⋂ i, {x : M | R (γ i) x} :=
      iInter_mono fun _ _ h => chartChronology_subset_chartCausalRelation o h
    rw [hNoFuture] at hSub
    rw [subset_empty_iff.mp hSub, measure_empty]
  let γrev : ιᵒᵈ → M := γ
  have hNoPast : (⋂ i, {x : M | R x (γrev i)}) = ∅ := by
    apply iInter_future_eq_empty_of_no_limit (fun a b => R b a) γrev (fun h => hOrd h) ?_ ?_ hPast
    · intro x U hU
      obtain ⟨V, hV, hSub, hConv⟩ := hLoc x U hU
      refine ⟨V, hV, hSub, ?_⟩
      intro a z b ha hb haz hzb
      exact hConv hb ha hzb haz
    · intro a b
      simpa only [and_comm] using hDiam b a
  have hPempty : μ (⋂ i : ιᵒᵈ, P i) = 0 := by
    have hSub : (⋂ i : ιᵒᵈ, P i) ⊆ ⋂ i, {x : M | R x (γrev i)} :=
      iInter_mono fun _ _ h => chartChronology_subset_chartCausalRelation o h
    rw [hNoPast] at hSub
    rw [subset_empty_iff.mp hSub, measure_empty]
  exact ⟨logarithmic_volume_time_tendsto_atBot (ι := ιᵒᵈ) μ hP.dual_left hF.dual_left
      hPmeas hBefore hAfter hPempty,
    logarithmic_volume_time_tendsto_atTop μ hP hF hFmeas hBefore hAfter hFempty⟩

end Burnett.Geometry.FiniteCausalVolume
