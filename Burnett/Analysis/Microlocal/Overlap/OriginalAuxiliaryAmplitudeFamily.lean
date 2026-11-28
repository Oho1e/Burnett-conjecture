import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeWeightedPushforward
import Burnett.Analysis.Microlocal.Overlap.OriginalReceivingLocalClassicalAssembly

/-! All auxiliary changes of the original covariance on one extraction. -/
set_option autoImplicit false
set_option maxRecDepth 4600
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Set Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection fromAmbient map_fromAmbient_eq_of_unitNull)
open Burnett.Geometry.CotangentAngularExtension (cotangentNorm)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeFiber)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff ENNReal Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M] [T2Space M]

/-- Choose the extraction, its actual chart witnesses, and the original
covariance and null measure before choosing a receiving auxiliary metric.
Every receiving measure uses that extraction and the same chart data. -/
theorem exists_originalVacuum_intrinsicAmplitude_weightedPushforward_allAuxiliaryMetrics_sameWitnesses
    [Nonempty M] (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
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
            ∃ A : IntrinsicAmplitudeCovariance r, ∃ μ : Measure (Cosphere r),
              HasOriginalIntrinsicAmplitude r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
              HasOriginalReceivingLocalClassicalPairings r B g hB hg hSig.isNondegenerate (s ∘ t) A ∧
              HasIntrinsicPhysicalContraction r B hSig.isNondegenerate A μ ∧
              ∀ r' : Metric (M := M),
                ∃ A' : IntrinsicAmplitudeCovariance r', ∃ μ' : Measure (Cosphere r'),
                  HasOriginalIntrinsicAmplitude r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
                  HasOriginalReceivingLocalClassicalPairings r' B g hB hg hSig.isNondegenerate (s ∘ t) A' ∧
                  HasIntrinsicPhysicalContraction r' B hSig.isNondegenerate A' μ' ∧
                  HasIntrinsicAmplitudeWeightedPushforward r r' A A' ∧
                  (∀ (L : ∀ p : Cosphere r', AmplitudeFiber (projection p) →ₗ[ℝ] ℂ),
                    Integrable (fun p => L p (A'.density p)) A'.control →
                    A'.control.withDensityᵥ (fun p => L p (A'.density p)) =
                      (A.control.withDensityᵥ (fun p => (cotangentNorm r' p.val ^ 2) •
                        pullbackAmplitudeFiberTest r r' L p (A.density p))).map
                          (renormalizeUnitCosphere r r')) ∧
                  μ' = (μ.withDensity (fun p => ENNReal.ofReal (cotangentNorm r' p.val ^ 2))).map
                    (renormalizeUnitCosphere r r') := by
  letI : MeasurableSpace (CotangentBundle M) := borel _
  letI : BorelSpace (CotangentBundle M) := ⟨rfl⟩
  obtain ⟨t, ht, q, hCover, ν, hf, hRep, m, hmLoc, hmReg, hmNull, hmFin, hmChart⟩ :=
    exists_originalVacuum_globalPhysicalMeasure r B g hB hg hSig hsG hnG hconv hb hv s hs
  have hσ := hs.comp ht
  have hRaw (i : ℕ) := (hRep i).1
  have originalAmplitude (aux : Metric (M := M))
      (hConv : LocallyUniformlyConverges aux g B) (hBound : AuxiliaryAdmissibility.CompactDhBound aux B g)
      (C : IntrinsicAmplitudeCovariance aux) (hLoc : IsLocallyFiniteMeasure C.control)
      (hFin : ∀ K : Set M, IsCompact K → C.control (projection ⁻¹' K) < ⊤)
      (hLaws : HasOriginalAmplitudeChartLaws aux B g hB hg hSig.isNondegenerate (s ∘ t) C) :
      HasOriginalIntrinsicAmplitude aux B g hB hg hSig.isNondegenerate (s ∘ t) C ∧
        HasOriginalReceivingLocalClassicalPairings aux B g hB hg hSig.isNondegenerate (s ∘ t) C := by
    letI : IsLocallyFiniteMeasure C.control := hLoc
    have hIntrinsic : HasOriginalIntrinsicAmplitude aux B g hB hg hSig.isNondegenerate (s ∘ t) C := by
      refine ⟨fun _ => ⟨q, hCover, ν, hf, hRep⟩, hLoc, regular_measure_on_unitCosphere aux C.control,
        hFin, hLaws, ?_⟩
      filter_upwards [hLaws.ae_global_positive_unitTrace_ricciKernel hSig.isSymmetric hsG hnG
        hConv hBound hv hσ q hCover ν hf hRaw,
        hLaws.ae_intrinsicAmplitudeRicciKernel hSig.isSymmetric hsG hnG hConv hBound hv hσ q hCover ν hf hRaw]
        with p hp hKernel
      exact ⟨hp.1, fun b => (hp.2.1 b).1, hKernel⟩
    exact ⟨hIntrinsic, hasOriginalReceivingLocalClassicalPairings_of_intrinsicAmplitude
      aux B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hConv hBound hv (s ∘ t) hσ C hIntrinsic⟩
  have physicalContraction (aux : Metric (M := M))
      (hConv : LocallyUniformlyConverges aux g B) (hBound : AuxiliaryAdmissibility.CompactDhBound aux B g)
      (ambient : Measure (CotangentBundle M))
      (hData : OriginalGlobalPhysicalMeasureData aux B g hB hg hSig.isNondegenerate (s ∘ t) ambient)
      (C : IntrinsicAmplitudeCovariance aux)
      (hLaws : HasOriginalAmplitudeChartLaws aux B g hB hg hSig.isNondegenerate (s ∘ t) C) :
      HasIntrinsicPhysicalContraction aux B hSig.isNondegenerate C (fromAmbient aux ambient) := by
    have hMap := map_fromAmbient_eq_of_unitNull aux B hSig.isNondegenerate ambient hData.2.2.1
    refine original_globalPhysicalContraction_of_chartLaws aux B g hB hg hSig hsG hnG
      hConv hBound hv (s ∘ t) hσ q hCover ν hf hRaw C hLaws (fromAmbient aux ambient) ?_
    intro i
    rw [hMap]
    exact hData.2.2.2.2 (q i) (ν i) (hf i) (hRaw i)
  obtain ⟨A, hLocal, hFinite, hLaws⟩ := original_globalIntrinsicAmplitude_of_representedCharts
    r B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv hb hv (s ∘ t) hσ q hCover ν hf hRaw
  obtain ⟨hA, hPairs⟩ := originalAmplitude r hconv hb A hLocal hFinite hLaws
  have hData : OriginalGlobalPhysicalMeasureData r B g hB hg hSig.isNondegenerate (s ∘ t) m :=
    ⟨hmLoc, hmReg, hmNull, hmFin, hmChart⟩
  refine ⟨t, ht, hσ, q, hCover, ν, hf, hRep, A, fromAmbient r m, hA, hPairs,
    physicalContraction r hconv hb m hData A hLaws, ?_⟩
  intro r'
  have hconv' := AuxiliaryAdmissibility.locallyUniformlyConverges_changeAuxiliary r r' g B hconv
  have hb' := AuxiliaryAdmissibility.compactDhBound_changeAuxiliary r r' B g hB hg hconv hb
  obtain ⟨m', hmLoc', hmReg', hmNull', hmFin', hmChart'⟩ := exists_glued_originalVacuum_physicalMeasure
    r' B g hB hg hSig hsG hnG hconv' hb' hv q hCover (s ∘ t) hσ ν hf hRaw
  have hData' : OriginalGlobalPhysicalMeasureData r' B g hB hg hSig.isNondegenerate (s ∘ t) m' :=
    ⟨hmLoc', hmReg', hmNull', hmFin', hmChart'⟩
  have hAmbient := original_globalPhysicalMeasure_changeAuxiliary_of_chartLaws
    r r' B g hB hg hSig hsG hnG hconv hb hv q hCover (s ∘ t) hσ ν hf hRaw m m' (fun i =>
      ⟨hmChart (q i) (ν i) (hf i) (hRaw i), hmChart' (q i) (ν i) (hf i) (hRaw i)⟩)
  obtain ⟨A', hLocal', hFinite', hLaws'⟩ := original_globalIntrinsicAmplitude_of_representedCharts
    r' B g hB hg hSig.isSymmetric hsG hSig.isNondegenerate hnG hconv' hb' hv (s ∘ t) hσ q hCover ν hf hRaw
  obtain ⟨hA', hPairs'⟩ := originalAmplitude r' hconv' hb' A' hLocal' hFinite' hLaws'
  obtain ⟨hTrace, hPos, hControl, hDensity⟩ := original_globalIntrinsicAmplitude_trace_changeAuxiliary
    r r' B g hB hg hSig hsG hnG hconv hb hv (s ∘ t) hσ q hCover ν hf hRaw A A' hLaws hLaws'
  have hWeighted := hasIntrinsicAmplitudeWeightedPushforward_of_traceChange r r' A A'
    hTrace hPos hControl hDensity
  refine ⟨A', fromAmbient r' m', hA', hPairs', physicalContraction r' hconv' hb' m' hData' A' hLaws',
    hWeighted, intrinsicAmplitude_testMeasure_changeAuxiliary r r' A A' hWeighted, ?_⟩
  simpa only [cotangentAuxiliaryWeight_eq_ofReal_norm_sq_on_cosphere] using
    fromAmbient_changeAuxiliary r r' B hSig.isNondegenerate m m' hmNull hmNull' hAmbient

end Burnett.Microlocal.Overlap
