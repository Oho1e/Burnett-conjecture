import Burnett.Geometry.Causality.ChartChronologicalNull

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open MeasureTheory Set
open scoped ENNReal ContDiff Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear

variable {M : Type*} [TopologicalSpace M]

private theorem isOpen_past_section {I : Set (M × M)} (hI : IsOpen I) (p : M) :
    IsOpen (sectionAt I p) := hI.preimage (continuous_id.prodMk continuous_const)

variable [MeasurableSpace M] [BorelSpace M]

/-- A chronological step detects a strictly larger past volume whenever it
admits an intermediate chronological point and the relation is irreflexive. -/
theorem past_volume_strict_of_step (μ : Measure M) [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    {I : Set (M × M)} (hI : IsOpen I)
    (hTrans : ∀ {a b c : M}, (a, b) ∈ I → (b, c) ∈ I → (a, c) ∈ I)
    (hIrrefl : ∀ a, (a, a) ∉ I) {a b : M} (hab : (a, b) ∈ I)
    (hmid : ∃ c, (a, c) ∈ I ∧ (c, b) ∈ I) :
    μ (sectionAt I a) < μ (sectionAt I b) := by
  let U := ((fun c : M => (a, c)) ⁻¹' I) ∩ sectionAt I b
  have hU : IsOpen U := (hI.preimage (continuous_const.prodMk continuous_id)).inter
    (isOpen_past_section hI b)
  obtain ⟨c, hac, hcb⟩ := hmid
  exact measure_lt_of_open_gap μ (isOpen_past_section hI a).measurableSet
    (fun _ hx => hTrans hx hab) hU ⟨c, hac, hcb⟩
    (fun x hx => ⟨hx.2, fun hxa => hIrrefl x (hTrans hxa hx.1)⟩)

variable [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M] [SecondCountableTopology M]

/-- The boundary of each chronological past has zero volume. Openness and
transitivity move any passing timelike chord into the interior. -/
theorem past_boundary_zero (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    {I : Set (M × M)} (hI : IsOpen I)
    (hTrans : ∀ {a b c : M}, (a, b) ∈ I → (b, c) ∈ I → (a, c) ∈ I)
    (hChord : ∀ a b, HasTimelikeChartChord g a b → (a, b) ∈ I ∨ (b, a) ∈ I)
    (p : M) : ManifoldVolume.geometricMeasure g (closure (sectionAt I p) \ sectionAt I p) = 0 := by
  let A := sectionAt I p
  have hA := isOpen_past_section hI p
  have hPush {a b : M} (hab : (a, b) ∈ I) (hb : b ∈ closure A) : a ∈ A := by
    let U := (fun c : M => (a, c)) ⁻¹' I
    have hU : IsOpen U := hI.preimage (continuous_const.prodMk continuous_id)
    obtain ⟨c, hac, hcp⟩ := mem_closure_iff.mp hb U hU hab
    exact hTrans hac hcp
  apply geometricVolume_zero_of_no_timelike_chart_chord g hg hL
    (isClosed_closure.measurableSet.diff hA.measurableSet)
  intro a ha b hb hseg
  rcases hChord a b hseg with hab | hba
  · exact ha.2 (hPush hab hb.1)
  · exact hb.2 (hPush hba ha.1)

/-- A closed causal relation bounded by the closures of chronological pasts
gives continuity of the past volume for any absolutely continuous finite measure. -/
theorem continuous_past_volume_of_closed_causal_relation
    (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    (μ : Measure M) [IsFiniteMeasure μ] (hμ : μ ≪ ManifoldVolume.geometricMeasure g)
    {I J : Set (M × M)} (hI : IsOpen I) (hJ : IsClosed J) (hIJ : I ⊆ J)
    (hTrans : ∀ {a b c : M}, (a, b) ∈ I → (b, c) ∈ I → (a, c) ∈ I)
    (hChord : ∀ a b, HasTimelikeChartChord g a b → (a, b) ∈ I ∨ (b, a) ∈ I)
    (hClose : ∀ p, sectionAt J p ⊆ closure (sectionAt I p)) :
    Continuous (fun p => μ (sectionAt I p)) := by
  refine continuous_iff_continuousAt.mpr fun p => continuousAt_section_volume μ hI hJ hIJ p ?_
  have hSub : sectionAt J p \ sectionAt I p ⊆ closure (sectionAt I p) \ sectionAt I p :=
    fun _ hp => ⟨hClose p hp.1, hp.2⟩
  exact measure_mono_null hSub (hμ (past_boundary_zero g hg hL hI hTrans hChord p))

/-- The geometric volume class supplies a continuous logarithmic volume time
when the causal sections have the two closure properties of global hyperbolicity. -/
theorem exists_logarithmic_volume_time [T2Space M]
    (g : Field (M := M)) (hg : IsSmooth g) (hL : HasLorentzSignature g)
    {I J : Set (M × M)} (hI : IsOpen I) (hJ : IsClosed J) (hIJ : I ⊆ J)
    (hTrans : ∀ {a b c : M}, (a, b) ∈ I → (b, c) ∈ I → (a, c) ∈ I)
    (hIrrefl : ∀ a, (a, a) ∉ I)
    (hChord : ∀ a b, HasTimelikeChartChord g a b → (a, b) ∈ I ∨ (b, a) ∈ I)
    (hSteps : ∀ {a b : M}, (a, b) ∈ I → ∃ c, (a, c) ∈ I ∧ (c, b) ∈ I)
    (hBefore : ∀ p, (sectionAt I p).Nonempty)
    (hAfter : ∀ p, (sectionAt (Prod.swap ⁻¹' I) p).Nonempty)
    (hClosePast : ∀ p, sectionAt J p ⊆ closure (sectionAt I p))
    (hCloseFuture : ∀ p, sectionAt (Prod.swap ⁻¹' J) p ⊆ closure (sectionAt (Prod.swap ⁻¹' I) p)) :
    ∃ μ : Measure M, IsFiniteMeasure μ ∧ μ.IsOpenPosMeasure ∧
      ManifoldVolume.geometricMeasure g ≪ μ ∧ μ ≪ ManifoldVolume.geometricMeasure g ∧
      let T := fun p => Real.log (μ (sectionAt I p)).toReal -
        Real.log (μ (sectionAt (Prod.swap ⁻¹' I) p)).toReal
      Continuous T ∧ ∀ {a b : M}, (a, b) ∈ I → T a < T b := by
  obtain ⟨μ, hFin, hPos, hVμ, hμV⟩ := exists_finite_equivalent_volume g hg hL.isNondegenerate
  letI := hFin
  letI := hPos
  let Irev := Prod.swap ⁻¹' I
  have hRev : IsOpen Irev := hI.preimage continuous_swap
  have hTransRev {a b c : M} (hab : (a, b) ∈ Irev) (hbc : (b, c) ∈ Irev) : (a, c) ∈ Irev :=
    hTrans hbc hab
  have hPastCont := continuous_past_volume_of_closed_causal_relation g hg hL μ hμV
    hI hJ hIJ (fun h₁ h₂ => hTrans h₁ h₂) hChord hClosePast
  have hFutureCont := continuous_past_volume_of_closed_causal_relation g hg hL μ hμV
    hRev (hJ.preimage continuous_swap) (preimage_mono hIJ) (fun h₁ h₂ => hTransRev h₁ h₂)
    (fun a b h => (hChord a b h).symm) hCloseFuture
  have hPositive {S : Set M} (hS : IsOpen S) (hne : S.Nonempty) : 0 < (μ S).toReal :=
    ENNReal.toReal_pos (hS.measure_ne_zero μ hne) (measure_ne_top μ S)
  have hContLog {R : Set (M × M)} (hR : IsOpen R) (hne : ∀ p, (sectionAt R p).Nonempty)
      (hCont : Continuous fun p => μ (sectionAt R p)) :
      Continuous fun p => Real.log (μ (sectionAt R p)).toReal := by
    apply continuous_iff_continuousAt.mpr
    intro p
    have hAt : ContinuousAt (fun q => μ (sectionAt R q)) p := hCont.continuousAt
    have hReal : ContinuousAt (fun q => (μ (sectionAt R q)).toReal) p :=
      ContinuousAt.comp' (f := fun q : M => μ (sectionAt R q))
        (ENNReal.continuousAt_toReal (measure_ne_top μ (sectionAt R p))) hAt
    exact ContinuousAt.comp' (f := fun q : M => (μ (sectionAt R q)).toReal)
      (Real.continuousAt_log (hPositive (isOpen_past_section hR p) (hne p)).ne') hReal
  refine ⟨μ, hFin, hPos, hVμ, hμV, (hContLog hI hBefore hPastCont).sub
    (hContLog hRev hAfter hFutureCont), ?_⟩
  intro a b hab
  obtain ⟨c, hac, hcb⟩ := hSteps hab
  have hp := past_volume_strict_of_step μ hI (fun h₁ h₂ => hTrans h₁ h₂) hIrrefl hab ⟨c, hac, hcb⟩
  have hf := past_volume_strict_of_step μ hRev (fun h₁ h₂ => hTransRev h₁ h₂) hIrrefl
    (show (b, a) ∈ Irev from hab) ⟨c, hcb, hac⟩
  have hlogp := Real.log_lt_log (hPositive (isOpen_past_section hI a) (hBefore a))
    ((ENNReal.toReal_lt_toReal (measure_ne_top μ _) (measure_ne_top μ _)).2 hp)
  have hlogf := Real.log_lt_log (hPositive (isOpen_past_section hRev b) (hAfter b))
    ((ENNReal.toReal_lt_toReal (measure_ne_top μ _) (measure_ne_top μ _)).2 hf)
  exact sub_lt_sub hlogp hlogf

end Burnett.Geometry.FiniteCausalVolume
