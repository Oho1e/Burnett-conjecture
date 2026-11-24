import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliaryControl
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTraceReconstruction

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 1200000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude ae_originalVolume_auxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.F07.IntrinsicAmplitude (auxiliaryTraceLinear aemeasurable_auxiliaryTraceLinear
  chartAuxiliaryInverse_posDef auxiliaryTrace_normalization_recovers_entry_measures)
open scoped ContDiff Manifold ENNReal Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- Normalize the original positive amplitude by its actual auxiliary trace.
On a compact part of its nonzero base, the trace-normalized density is positive
with unit trace, and it recovers every one of the original weighted complex
entry measures on the true cosphere. -/
theorem original_compactChart_traceNormalizedAmplitude
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    let W := amplitudeCosphereWindow r K
    let τ := (chartAmplitudeTraceControl r q ν hf).restrict W
    let A := liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf)
    let D (p : Cosphere r) := (chartAmplitudeTraceWeight r q ν hf p)⁻¹ • A p
    (∀ᵐ p ∂τ, (D p).PosSemidef ∧ auxiliaryTraceLinear (liftChartAuxiliaryInverse r q p) (D p) = 1) ∧
      ∀ i j : Pair, Integrable (fun p => D p i j) τ ∧
        τ.withDensityᵥ (fun p => D p i j) = normalizedCosphereAmplitudeEntryOn r q ν hf i j K := by
  intro W τ A D
  let μ := (chartCosphereControlMeasure r q ν).restrict W
  let R := liftChartAuxiliaryInverse r q
  let φ := chartAuxiliaryCosphere r q
  let U := amplitudeChartWindow r q K
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hPos : ∀ᵐ p ∂μ, Matrix.PosDef (R p) ∧ (A p).PosSemidef := by
    have hφ : MeasurableEmbedding φ := measurableEmbedding_chartAuxiliaryCosphere r q
    have hlift : ∀ᵐ z ∂traceMeasure ν, Matrix.PosDef (R (φ z)) ∧ (A (φ z)).PosSemidef := by
      filter_upwards [ae_originalVolume_auxiliaryAmplitude r B g hB hg hsB hsG hnB hnG
        hconv hbnd hv q σ hσ ν hf hRep] with z hz
      change Matrix.PosDef (liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r q z)) ∧
        (liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) (chartAuxiliaryCosphere r q z)).PosSemidef
      rw [liftChartAuxiliaryInverse_apply, liftChartAmplitude_apply]
      exact ⟨chartAuxiliaryInverse_posDef r q z, hz.1⟩
    change ∀ᵐ p ∂(chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K),
      Matrix.PosDef (R p) ∧ (A p).PosSemidef
    rw [chartCosphereControlMeasure_restrict r q ν hK.isClosed.measurableSet]
    apply hφ.ae_map_iff.mpr
    exact (withDensity_absolutelyContinuous ((traceMeasure ν).restrict U) (chartInverseCutoffSquare q)).ae_le
      (ae_restrict_of_ae hlift)
  have hEntry (i j : Pair) : Integrable (fun p => A p i j) μ ∧
      normalizedCosphereAmplitudeEntryOn r q ν hf i j K = μ.withDensityᵥ (fun p => A p i j) :=
    normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude r q ν (chartAuxiliaryAmplitude r q ν hf)
      hK.isClosed.measurableSet i j
      (integrable_normalizedCosphereAmplitudeEntry_on_compact r q ν hf i j hK hSub)
  have hTrace : AEMeasurable (chartAmplitudeTraceWeight r q ν hf) μ :=
    aemeasurable_auxiliaryTraceLinear μ R A
      (fun i j => (measurable_liftChartAuxiliaryInverse_entry r q i j).aemeasurable)
      (fun i j => (measurable_liftChartAmplitude_entry r q _ i j
        (measurable_chartAuxiliaryAmplitude_entry r q ν hf i j)).aemeasurable)
  have hτ : τ = μ.withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p)) := by
    change ((chartCosphereControlMeasure r q ν).withDensity
      (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p))).restrict W = _
    rw [restrict_withDensity hW]
  obtain ⟨hNormal, hRecovery⟩ := auxiliaryTrace_normalization_recovers_entry_measures μ R A
    hPos hTrace (fun i j => (hEntry i j).1)
  rw [hτ]
  refine ⟨hNormal, fun i j => ?_⟩
  exact ⟨(hRecovery i j).1, (hRecovery i j).2.trans (hEntry i j).2.symm⟩

end Burnett.Microlocal.Overlap
