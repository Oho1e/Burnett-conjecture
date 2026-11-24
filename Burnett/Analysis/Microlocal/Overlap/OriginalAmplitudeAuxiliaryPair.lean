import Burnett.Analysis.Microlocal.Overlap.OriginalAuxiliaryGlobalExistence
import Burnett.Analysis.Microlocal.Overlap.GlobalOriginalAmplitudeContraction
import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitudeTraceChange

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 1450000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection fromAmbient map_fromAmbient_eq_of_unitNull)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- A single original extraction supplies both globally normalized amplitude
fields, both original physical contractions, and their radial change laws. -/
theorem exists_originalVacuum_sameWitnesses_intrinsicAmplitude_changeAuxiliary [Nonempty M]
    (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n))
    (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (s : ℕ → ℕ) (hs : StrictMono s) :
    ∃ t : ℕ → ℕ, StrictMono t ∧ StrictMono (s ∘ t) ∧
      ∃ q : ℕ → CompactChartInput M,
        (⋃ i, (q i).cutoffLocusAbove (1 / 2)) = univ ∧
        ∃ ν : ∀ i, (JetSlot → ℂ) → Measure (Chart (q i).ball),
          ∃ hf : ∀ i v, IsFiniteMeasure (ν i v),
            (∀ i, let c := q i
              RepresentsCompactJetPairings c.ball
                (originalGradient_volumeWeightedL2 B g hB hg hSig.isNondegenerate c.center c.cutoff
                  (c.cutoff_support.trans c.ball_in_chart)) (s ∘ t) (ν i) (hf i) ∧
              Burnett.P01.RepresentsVolumeProjectedPairings B g c (s ∘ t) (ν i) (hf i)) ∧
            ∃ m m' : Measure (CotangentBundle M),
              OriginalGlobalPhysicalMeasureData r B g hB hg hSig.isNondegenerate (s ∘ t) m ∧
              OriginalGlobalPhysicalMeasureData r' B g hB hg hSig.isNondegenerate (s ∘ t) m' ∧
              m' = renormalizeCotangentPhysicalMeasure r' m ∧
              ∃ A : IntrinsicAmplitudeCovariance r, ∃ A' : IntrinsicAmplitudeCovariance r',
                let F := renormalizeUnitCosphere r r'
                let μ := fromAmbient r m
                let μ' := fromAmbient r' m'
                let newTrace := intrinsicAmplitudeTraceInMetric r r' A.density
                IsLocallyFiniteMeasure A.control ∧ IsLocallyFiniteMeasure A'.control ∧
                (∀ K : Set M, IsCompact K → A.control (projection ⁻¹' K) < ⊤) ∧
                (∀ K : Set M, IsCompact K → A'.control (projection ⁻¹' K) < ⊤) ∧
                HasOriginalAmplitudeChartLaws r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
                HasOriginalAmplitudeChartLaws r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
                AEMeasurable newTrace A.control ∧ (∀ᵐ p ∂A.control, 0 < newTrace p) ∧
                A'.control = (A.control.withDensity (fun p =>
                  cotangentAuxiliaryWeight r' p.val * ENNReal.ofReal (newTrace p))).map F ∧
                (∀ᵐ p ∂A.control, pullbackAmplitudeDensity r r' A'.density p =
                  (newTrace p)⁻¹ • A.density p) ∧
                μ.map (Subtype.val : Cosphere r → CotangentBundle M) = m ∧
                μ'.map (Subtype.val : Cosphere r' → CotangentBundle M) = m' ∧
                HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
                HasIntrinsicPhysicalContraction r' B hSig.isNondegenerate A' μ' ∧
                μ' = (μ.withDensity (fun p => cotangentAuxiliaryWeight r' p.val)).map F := by
  obtain ⟨t, ht, q, hCover, ν, hf, hReps, m, m', hData, hData', hAmbientChange⟩ :=
    exists_originalVacuum_globalPhysicalMeasure_changeAuxiliary_sameWitnesses
      r r' B g hB hg hSig hsG hnG hconv hb hv s hs
  have hSubsequence := hs.comp ht
  have hRaw (i : ℕ) := (hReps i).1
  have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
  have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
  obtain ⟨A, hLocal, hFinite, hLaws⟩ := original_globalIntrinsicAmplitude_of_representedCharts
    r B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv hb hv (s ∘ t) hSubsequence
    q hCover ν hf hRaw
  obtain ⟨A', hLocal', hFinite', hLaws'⟩ := original_globalIntrinsicAmplitude_of_representedCharts
    r' B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv' hb' hv (s ∘ t) hSubsequence
    q hCover ν hf hRaw
  obtain ⟨hTraceMeas, hTracePos, hControl, hDensity⟩ := original_globalIntrinsicAmplitude_trace_changeAuxiliary
    r r' B g hB hg hSig hsG hnG hconv hb hv (s ∘ t) hSubsequence q hCover ν hf hRaw A A' hLaws hLaws'
  let μ := fromAmbient r m
  let μ' := fromAmbient r' m'
  have hMap : μ.map (Subtype.val : Cosphere r → CotangentBundle M) = m :=
    map_fromAmbient_eq_of_unitNull r B hSig.isNondegenerate m hData.2.2.1
  have hMap' : μ'.map (Subtype.val : Cosphere r' → CotangentBundle M) = m' :=
    map_fromAmbient_eq_of_unitNull r' B hSig.isNondegenerate m' hData'.2.2.1
  have hPhysical := original_globalPhysicalContraction_of_chartLaws r B g hB hg hSig hsG hnG
    hconv hb hv (s ∘ t) hSubsequence q hCover ν hf hRaw A hLaws μ (fun i => by
      rw [hMap]
      exact hData.2.2.2.2 (q i) (ν i) (hf i) (hRaw i))
  have hPhysical' := original_globalPhysicalContraction_of_chartLaws r' B g hB hg hSig hsG hnG
    hconv' hb' hv (s ∘ t) hSubsequence q hCover ν hf hRaw A' hLaws' μ' (fun i => by
      rw [hMap']
      exact hData'.2.2.2.2 (q i) (ν i) (hf i) (hRaw i))
  have hPhysicalChange := fromAmbient_changeAuxiliary r r' B hSig.isNondegenerate m m'
    hData.2.2.1 hData'.2.2.1 hAmbientChange
  exact ⟨t, ht, hSubsequence, q, hCover, ν, hf, hReps, m, m', hData, hData', hAmbientChange,
    A, A', hLocal, hLocal', hFinite, hFinite', hLaws, hLaws', hTraceMeas, hTracePos, hControl, hDensity,
    hMap, hMap', hPhysical, hPhysical', hPhysicalChange⟩

end Burnett.Microlocal.Overlap
