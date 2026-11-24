import Burnett.Analysis.Microlocal.Overlap.AmbientAuxiliaryMeasureChange
import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalPhysicalMeasure

/-! One original subsequence and its witnesses give both global auxiliary physical measures. -/

set_option autoImplicit false
set_option maxHeartbeats 1550000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- The ambient measure properties and the law on every represented original chart,
at one fixed subsequence and auxiliary metric. -/
def OriginalGlobalPhysicalMeasureData
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B)
    (σ : ℕ → ℕ) (μ : Measure (CotangentBundle M)) : Prop :=
  IsLocallyFiniteMeasure μ ∧ μ.Regular ∧
    μ (cotangentUnitNull r B hnB)ᶜ = 0 ∧
    (∀ K : Set M, IsCompact K → μ ((fun p : CotangentBundle M => p.proj) ⁻¹' K) < ⊤) ∧
    ∀ (q : CompactChartInput M) (νq : (JetSlot → ℂ) → Measure (Chart q.ball))
        (hfq : ∀ v, IsFiniteMeasure (νq v)),
      RepresentsCompactJetPairings q.ball
        (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
          (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq →
      let S := (fun p : CotangentBundle M => p.proj) ⁻¹' q.nonzeroLocus
      μ.restrict S = (normalizedCotangentPhysicalMeasure q r B hnB νq hfq).restrict S

variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Construct the two global ambient measures from the very same original
subsequence and countable chart witnesses. Both have the full represented
chart law and the second is the weighted radial pushforward of the first. -/
theorem exists_originalVacuum_globalPhysicalMeasure_changeAuxiliary_sameWitnesses [Nonempty M]
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧
      ∃ charts : ℕ → CompactChartInput M,
        (⋃ i, (charts i).cutoffLocusAbove (1 / 2)) = univ ∧
        ∃ ν : ∀ i : ℕ, (JetSlot → ℂ) → Measure (Chart (charts i).ball),
          ∃ hfin : ∀ i v, IsFiniteMeasure (ν i v),
            (∀ i, let q := charts i
              RepresentsCompactJetPairings q.ball
                (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate q.center q.cutoff
                  (q.cutoff_support.trans q.ball_in_chart)) (s ∘ t) (ν i) (hfin i) ∧
              Burnett.P01.RepresentsVolumeProjectedPairings B g q (s ∘ t) (ν i) (hfin i)) ∧
            ∃ μ μ' : Measure (CotangentBundle M),
              OriginalGlobalPhysicalMeasureData r B g hB hg hSig.isNondegenerate (s ∘ t) μ ∧
              OriginalGlobalPhysicalMeasureData r' B g hB hg hSig.isNondegenerate (s ∘ t) μ' ∧
              μ' = renormalizeCotangentPhysicalMeasure r' μ := by
  obtain ⟨t, ht, charts, cover, ν, hfin, hReps, μ, hLoc, hReg, hNull, hFinite, hLaw⟩ :=
    exists_originalVacuum_globalPhysicalMeasure r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
  have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
  have hRaw := fun i => (hReps i).1
  obtain ⟨μ', hLoc', hReg', hNull', hFinite', hLaw'⟩ :=
    exists_glued_originalVacuum_physicalMeasure r' B g hB hg hSig hsG hnG hconv' hb' hv
      charts cover (s ∘ t) (hs.comp ht) ν hfin hRaw
  refine ⟨t, ht, charts, cover, ν, hfin, hReps, μ, μ',
    ⟨hLoc, hReg, hNull, hFinite, hLaw⟩, ⟨hLoc', hReg', hNull', hFinite', hLaw'⟩, ?_⟩
  exact original_globalPhysicalMeasure_changeAuxiliary_of_chartLaws r r' B g hB hg hSig hsG hnG
    hconv hb hv charts cover (s ∘ t) (hs.comp ht) ν hfin hRaw μ μ' (fun i =>
      ⟨hLaw (charts i) (ν i) (hfin i) (hRaw i), hLaw' (charts i) (ν i) (hfin i) (hRaw i)⟩)

/-- The two ambient chart laws and their change formula also hold when the base
is empty. -/
theorem exists_originalVacuum_globalPhysicalMeasures_changeAuxiliary
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n))
    (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ ∃ μ μ' : Measure (CotangentBundle M),
      OriginalGlobalPhysicalMeasureData r B g hB hg hSig.isNondegenerate (s ∘ t) μ ∧
      OriginalGlobalPhysicalMeasureData r' B g hB hg hSig.isNondegenerate (s ∘ t) μ' ∧
      μ' = renormalizeCotangentPhysicalMeasure r' μ := by
  by_cases hM : Nonempty M
  · letI : Nonempty M := hM
    obtain ⟨t, ht, _, _, _, _, _, μ, μ', hData, hData', hChange⟩ :=
      exists_originalVacuum_globalPhysicalMeasure_changeAuxiliary_sameWitnesses
        r r' B g hB hg hSig hsG hnG hconv hb hv s hs
    exact ⟨t, ht, μ, μ', hData, hData', hChange⟩
  · have hZero (u : Metric (M := M)) :
        OriginalGlobalPhysicalMeasureData u B g hB hg hSig.isNondegenerate (s ∘ id) 0 := by
        refine ⟨inferInstance, inferInstance, by simp, ?_, ?_⟩
        · intro K _
          simp
        · intro q
          exact (hM ⟨q.center⟩).elim
    exact ⟨id, strictMono_id, 0, 0, hZero r, hZero r', by simp [renormalizeCotangentPhysicalMeasure]⟩

end Burnett.Microlocal.Overlap
