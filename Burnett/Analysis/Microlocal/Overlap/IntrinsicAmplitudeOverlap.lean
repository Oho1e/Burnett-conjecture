import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliaryControl
import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeCoordinates

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 2000000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence UnitNullCompactness
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeCovarianceDensity chartAmplitude chartAmplitude_change fixedCotangentTransitionMatrix
    fixedCotangentTransitionMatrix_preferred)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors (roundOverlap tensorPairTransition)
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The four-slot density from a represented chart, divided by its own
intrinsic auxiliary trace. The control of that chart ignores the complement
of the chart image. -/
def chartNormalizedIntrinsicAmplitude (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v)) :
    AmplitudeCovarianceDensity r := by
  classical
  intro p
  let c : AtlasChart M := .atPoint q.center
  exact if h : projection p ∈ c.chart.source then
    chartAmplitude c (projection p) h ((chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
      liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p)
  else 0

theorem chartNormalizedIntrinsicAmplitude_of_mem (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (p : Cosphere r) (hp : projection p ∈ (chartAt CoordinateSpace q.center).source) :
    chartNormalizedIntrinsicAmplitude r q ν hf p =
      chartAmplitude (.atPoint q.center) (projection p) hp ((chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
        liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p) := by
  classical
  let c : AtlasChart M := .atPoint q.center
  let A := (chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
    liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p
  have hc : projection p ∈ c.chart.source := hp
  change (if h : projection p ∈ c.chart.source then chartAmplitude c (projection p) h A else 0) =
    chartAmplitude c (projection p) hc A
  rw [dif_pos hc]

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- The same original sequence determines the same intrinsic normalized
four-slot density on the common auxiliary trace of a compact overlap. -/
theorem original_compactOverlap_intrinsicAmplitude_agree
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (q d : CompactChartInput M)
    (νq : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfq : ∀ v, IsFiniteMeasure (νq v))
    (νd : (JetSlot → ℂ) → Measure (Chart d.ball)) (hfd : ∀ v, IsFiniteMeasure (νd v))
    (hRq : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ νq hfq)
    (hRd : RepresentsCompactJetPairings d.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB d.center d.cutoff
        (d.cutoff_support.trans d.ball_in_chart)) σ νd hfd)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus ∩ d.nonzeroLocus) :
    let U := amplitudeCosphereWindow r K
    let τq := (chartAmplitudeTraceControl r q νq hfq).restrict U
    let τd := (chartAmplitudeTraceControl r d νd hfd).restrict U
    τq = τd ∧ ∀ᵐ p ∂τq, chartNormalizedIntrinsicAmplitude r q νq hfq p =
      chartNormalizedIntrinsicAmplitude r d νd hfd p := by
  intro U τq τd
  obtain ⟨hControl, hMatrix⟩ := original_compactOverlap_amplitudeTraceControls_agree r B g
    hB hg hsB hsG hnB hnG hconv hb hv σ hσ q d νq hfq νd hfd hRq hRd hK hSub
  refine ⟨hControl, ?_⟩
  have hEqControl : τq = τd := hControl
  have hLift : ∀ᵐ p ∂τq, ∃ z ∈ amplitudeChartWindow r d K, chartAuxiliaryCosphere r d z = p := by
    rw [hEqControl]
    exact ae_chartAmplitudeTraceControl_restrict_exists_windowPoint r d νd hfd hK.isClosed.measurableSet
  filter_upwards [hMatrix, hLift] with p hEq hp
  obtain ⟨z, hz, rfl⟩ := hp
  let p := chartAuxiliaryCosphere r d z
  let x := projection p
  have hx : x ∈ K := hz
  have hq : x ∈ (chartAt CoordinateSpace q.center).source := (hSub hx).1.1
  have hd : x ∈ (chartAt CoordinateSpace d.center).source := (hSub hx).2.1
  let y : roundOverlap d q := ⟨z, amplitudeChartWindow_subset_roundOverlap r q d
    (hSub.trans inter_subset_left) hz⟩
  let D := tensorPairTransition (fixedCotangentTransitionMatrix (.atPoint d.center) (.atPoint q.center) x)
  let A := liftChartAmplitude r q (chartAuxiliaryAmplitude r q νq hfq) p
  let Q := chartAuxiliaryAmplitude r d νd hfd z
  let wq := (chartAmplitudeTraceWeight r q νq hfq p)⁻¹
  let wd := (chartAmplitudeTraceWeight r d νd hfd p)⁻¹
  have hT : receivingToSourceCotangent q d z.1 =
      fixedCotangentTransitionMatrix (.atPoint d.center) (.atPoint q.center) x :=
    (receivingToSourceCotangent_actual q d y).trans
      (fixedCotangentTransitionMatrix_preferred d.center q.center x).symm
  have hRep : (fun i j => transportedAmplitudeEntry r q d νd hfd i j z) = D * Q * Dᴴ := by
    change (fun i j => (tensorPairTransition (receivingToSourceCotangent q d z.1) * Q *
      (tensorPairTransition (receivingToSourceCotangent q d z.1))ᴴ) i j) = D * Q * Dᴴ
    rw [hT]
  change wq • A = wd • liftChartAmplitude r d
    (fun a i j => transportedAmplitudeEntry r q d νd hfd i j a) (chartAuxiliaryCosphere r d z) at hEq
  rw [liftChartAmplitude_apply, hRep] at hEq
  have hNorm : wq • A = D * (wd • Q) * Dᴴ := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul] using hEq
  change chartNormalizedIntrinsicAmplitude r q νq hfq p = chartNormalizedIntrinsicAmplitude r d νd hfd p
  rw [chartNormalizedIntrinsicAmplitude_of_mem r q νq hfq p hq,
      chartNormalizedIntrinsicAmplitude_of_mem r d νd hfd p hd]
  change chartAmplitude (.atPoint q.center) x hq (wq • A) =
    chartAmplitude (.atPoint d.center) x hd (wd • liftChartAmplitude r d
      (chartAuxiliaryAmplitude r d νd hfd) (chartAuxiliaryCosphere r d z))
  rw [hNorm, liftChartAmplitude_apply]
  exact chartAmplitude_change (.atPoint d.center) (.atPoint q.center) x hd hq (wd • Q)

end Burnett.Microlocal.Overlap
