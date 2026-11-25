import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeWeightedPushforward
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly

/-! The actual covariance and null measure change auxiliary section on the
same original extraction, with the classical local pairings in both metrics. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 3000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection fromAmbient)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- Both paper pushforwards on the same actual original witnesses. Every
locally represented classical test is read on the same subsequence for the
two auxiliary metrics. -/
theorem exists_originalVacuum_sameWitnesses_intrinsicAmplitude_weightedPushforward
    [Nonempty M] (r r' : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hSig : HasLorentzSignature B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
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
                (∀ p : Cosphere r, projection (F p) = projection p) ∧
                HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
                HasOriginalIntrinsicAmplitude r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
                HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
                HasOriginalReceivingLocalClassicalPairings r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
                HasIntrinsicAmplitudeWeightedPushforward r r' A A' ∧
                μ.map (Subtype.val : Cosphere r → CotangentBundle M) = m ∧
                μ'.map (Subtype.val : Cosphere r' → CotangentBundle M) = m' ∧
                HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
                HasIntrinsicPhysicalContraction r' B hSig.isNondegenerate A' μ' ∧
                μ' = (μ.withDensity (fun p => cotangentAuxiliaryWeight r' p.val)).map F := by
  obtain ⟨t, ht, hσ, q, hCover, ν, hf, hRep, m, m', hData, hData', hAmbient, A, A',
    hLocal, hLocal', hFinite, hFinite', hLaws, hLaws', hTraceMeas, hTracePos, hControl, hDensity,
    hMap, hMap', hPhysical, hPhysical', hμ⟩ :=
    exists_originalVacuum_sameWitnesses_intrinsicAmplitude_changeAuxiliary
      r r' B g hB hg hSig hsG hnG hconv hb hv s hs
  have hAmplitude (aux : Metric (M := M))
      (hC : LocallyUniformlyConverges aux g B) (hD : AuxiliaryAdmissibility.CompactDhBound aux B g)
      (Aaux : IntrinsicAmplitudeCovariance aux) (hLoc : IsLocallyFiniteMeasure Aaux.control)
      (hFin : ∀ K : Set M, IsCompact K → Aaux.control (projection ⁻¹' K) < ⊤)
      (hLaw : HasOriginalAmplitudeChartLaws aux B g hB hg hSig.isNondegenerate (s ∘ t) Aaux) :
      HasOriginalIntrinsicAmplitude aux B g hB hg hSig.isNondegenerate (s ∘ t) Aaux := by
    letI : IsLocallyFiniteMeasure Aaux.control := hLoc
    have hRaw (i : ℕ) := (hRep i).1
    refine ⟨fun _ => ⟨q, hCover, ν, hf, hRep⟩, hLoc, regular_measure_on_unitCosphere aux Aaux.control,
      hFin, hLaw, ?_⟩
    filter_upwards [hLaw.ae_global_positive_unitTrace_ricciKernel hSig.isSymmetric hsG hnG
      hC hD hv hσ q hCover ν hf hRaw,
      hLaw.ae_intrinsicAmplitudeRicciKernel hSig.isSymmetric hsG hnG hC hD hv hσ q hCover ν hf hRaw]
      with p hp hK
    exact ⟨hp.1, fun b => (hp.2.1 b).1, hK⟩
  have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
  have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
  have hA := hAmplitude r hconv hb A hLocal hFinite hLaws
  have hA' := hAmplitude r' hconv' hb' A' hLocal' hFinite' hLaws'
  have hPair := hasOriginalReceivingLocalClassicalPairings_of_intrinsicAmplitude
    r B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv hb hv (s ∘ t) hσ A hA
  have hPair' := hasOriginalReceivingLocalClassicalPairings_of_intrinsicAmplitude
    r' B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv' hb' hv (s ∘ t) hσ A' hA'
  have hWeighted := hasIntrinsicAmplitudeWeightedPushforward_of_traceChange r r' A A'
    hTraceMeas hTracePos hControl hDensity
  exact ⟨t, ht, hσ, q, hCover, ν, hf, hRep, m, m', hData, hData', hAmbient, A, A',
    renormalizeUnitCosphere_projection r r', hA, hA', hPair, hPair', hWeighted,
    hMap, hMap', hPhysical, hPhysical', hμ⟩

end Burnett.Microlocal.Overlap
