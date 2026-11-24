import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliaryControl

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 1100000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude ae_originalVolume_auxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector roundCovector)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped ContDiff Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]

/-- With respect to the same positive auxiliary trace control, the normalized
original chart amplitude retains the symmetric complex vacuum Ricci kernel
at the true auxiliary covector. Each point is represented in the given
measurable base window of the original chart. -/
theorem original_chart_traceNormalizedAmplitude_ae_ricciKernel
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
    {K : Set M} (hK : MeasurableSet K) :
    let τ := (chartAmplitudeTraceControl r q ν hf).restrict (amplitudeCosphereWindow r K)
    let D (p : Cosphere r) := (chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
      liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p
    ∀ᵐ p ∂τ, ∃ z ∈ amplitudeChartWindow r q K, chartAuxiliaryCosphere r q z = p ∧
      ∀ v : Pair → ℂ,
        let k (a b : Index) := (D p *ᵥ v) (a, b)
        let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
        IsSymmetricComplexTensor k ∧
          ∀ a b, complexRicciSymbol (backgroundInverse B q.center z.1) η k a b = 0 := by
  intro τ D
  let φ := chartAuxiliaryCosphere r q
  let U := amplitudeChartWindow r q K
  have hφ : MeasurableEmbedding φ := measurableEmbedding_chartAuxiliaryCosphere r q
  have hW := measurableSet_amplitudeCosphereWindow r hK
  have hU : MeasurableSet U := measurableSet_amplitudeChartWindow r q hK
  have hτ : τ = ((chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K)).withDensity
      (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p)) := by
    change ((chartCosphereControlMeasure r q ν).withDensity _).restrict
      (amplitudeCosphereWindow r K) = _
    rw [restrict_withDensity hW]
  rw [hτ]
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [chartCosphereControlMeasure_restrict r q ν hK]
  apply hφ.ae_map_iff.mpr
  apply (withDensity_absolutelyContinuous _ _).ae_le
  have horiginal := ae_originalVolume_auxiliaryAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hbnd hv q σ hσ ν hf hRep
  filter_upwards [ae_restrict_mem (μ := traceMeasure ν) hU, ae_restrict_of_ae (s := U) horiginal]
    with z hz hOriginal
  refine ⟨z, hz, rfl, fun v => ?_⟩
  let t := (chartAmplitudeTraceWeight r q ν hf (φ z))⁻¹
  let A := chartAuxiliaryAmplitude r q ν hf z
  have hVec : D (φ z) *ᵥ v = A *ᵥ (t • v) := by
    change (t • liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf)
      (chartAuxiliaryCosphere r q z)) *ᵥ v = _
    rw [liftChartAmplitude_apply, smul_mulVec, mulVec_smul]
  rw [hVec]
  exact hOriginal.2.2.2 (t • v)

end Burnett.Microlocal.Overlap
