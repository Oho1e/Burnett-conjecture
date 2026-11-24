import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeCommonControl
import Burnett.Analysis.Microlocal.Overlap.MeasurableLiftedChartAmplitude
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTraceCommonControlConsumer
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTraceTransport

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors
  (roundOverlap roundOverlapTransition chartAuxiliaryRay_roundOverlapTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.F07.IntrinsicAmplitude (auxiliaryTraceLinear auxiliaryTraceLinear_roundOverlap
  normalization_agrees_on_common_auxiliary_control)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The real trace of the actual chart amplitude in both inverse auxiliary
metric factors, evaluated on the true auxiliary unit cosphere. -/
def chartAmplitudeTraceWeight (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (p : Cosphere r) : ℝ :=
  auxiliaryTraceLinear (liftChartAuxiliaryInverse r q p)
    (liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p)

/-- Each chart's own positive auxiliary trace control in the cutoff-normalized
representation. It may be restricted to the compact overlap without changing
the density. -/
def chartAmplitudeTraceControl (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v)) :
    Measure (Cosphere r) :=
  (chartCosphereControlMeasure r q ν).withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p))

/-- A receiving chart point over the source nonzero locus admits the actual
inverse round chart transition. -/
theorem amplitudeChartWindow_subset_roundOverlap
    (r : Metric (M := M)) (q d : CompactChartInput M)
    {K : Set M} (hK : K ⊆ q.nonzeroLocus) :
    amplitudeChartWindow r d K ⊆ roundOverlap d q := by
  intro z hz
  have hq : (chartAt CoordinateSpace d.center).symm z.1 ∈ q.nonzeroLocus := hK hz
  exact ⟨⟨d.ball_in_chart z.1.property, hq.1⟩,
    interior_subset (q.chart_mem_interior_of_mem_nonzeroLocus hq)⟩

/-- The two inverse-chart representations of a round overlap point lift to
the same oriented point of the true auxiliary cosphere. -/
theorem chartAuxiliaryCosphere_roundOverlapTransition
    (r : Metric (M := M)) (q d : CompactChartInput M) (z : roundOverlap q d) :
    chartAuxiliaryCosphere r d (roundOverlapTransition q d z).1 = chartAuxiliaryCosphere r q z.1 :=
  Subtype.ext (chartAuxiliaryRay_roundOverlapTransition r q d z)

variable [T2Space M] [MeasurableSpace M] [BorelSpace M]

/-- The restricted auxiliary trace control is carried by points that have an
actual round-chart representative in the chosen base window. -/
theorem ae_chartAmplitudeTraceControl_restrict_exists_windowPoint
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    {K : Set M} (hK : MeasurableSet K) :
    ∀ᵐ p ∂(chartAmplitudeTraceControl r q ν hf).restrict (amplitudeCosphereWindow r K),
      ∃ z ∈ amplitudeChartWindow r q K, chartAuxiliaryCosphere r q z = p := by
  have hW := measurableSet_amplitudeCosphereWindow r hK
  have hU := measurableSet_amplitudeChartWindow r q hK
  rw [chartAmplitudeTraceControl, restrict_withDensity hW]
  apply (withDensity_absolutelyContinuous _ _).ae_le
  rw [chartCosphereControlMeasure_restrict r q ν hK]
  apply (measurableEmbedding_chartAuxiliaryCosphere r q).ae_map_iff.mpr
  exact (withDensity_absolutelyContinuous _ _).ae_le
    ((ae_restrict_mem (μ := traceMeasure ν) hU).mono fun z hz => ⟨z, hz, rfl⟩)

/-- On the receiving trace, computing the auxiliary trace after converting
to the source frame gives the receiving chart's own auxiliary trace. -/
theorem chartAmplitudeTraceWeight_ae_of_transport
    (r : Metric (M := M)) (q d : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart d.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    {K : Set M} (hK : MeasurableSet K) (hSub : K ⊆ q.nonzeroLocus) :
    let μ := (chartCosphereControlMeasure r d ν).restrict (amplitudeCosphereWindow r K)
    let D := liftChartAmplitude r d (fun z i j => transportedAmplitudeEntry r q d ν hf i j z)
    (fun p => auxiliaryTraceLinear (liftChartAuxiliaryInverse r q p) (D p))
      =ᵐ[μ] chartAmplitudeTraceWeight r d ν hf := by
  intro μ D
  let φ := chartAuxiliaryCosphere r d
  let U := amplitudeChartWindow r d K
  have hφ : MeasurableEmbedding φ := measurableEmbedding_chartAuxiliaryCosphere r d
  have hU : MeasurableSet U := measurableSet_amplitudeChartWindow r d hK
  have hμ : μ = (((traceMeasure ν).restrict U).withDensity (chartInverseCutoffSquare d)).map φ :=
    chartCosphereControlMeasure_restrict r d ν hK
  have hpt (y : Chart d.ball) (hy : y ∈ U) :
      auxiliaryTraceLinear (liftChartAuxiliaryInverse r q (φ y)) (D (φ y)) =
        chartAmplitudeTraceWeight r d ν hf (φ y) := by
    let z : roundOverlap d q := ⟨y, amplitudeChartWindow_subset_roundOverlap r q d hSub hy⟩
    let yq := (roundOverlapTransition d q z).1
    have hSame : chartAuxiliaryCosphere r q yq = φ y :=
      chartAuxiliaryCosphere_roundOverlapTransition r d q z
    have hR : liftChartAuxiliaryInverse r q (φ y) = chartAuxiliaryInverse r q yq.1 := by
      rw [← hSame, liftChartAuxiliaryInverse_apply]
    change auxiliaryTraceLinear (liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r d y))
        (liftChartAmplitude r d (fun z i j => transportedAmplitudeEntry r q d ν hf i j z)
          (chartAuxiliaryCosphere r d y)) =
      auxiliaryTraceLinear (liftChartAuxiliaryInverse r d (chartAuxiliaryCosphere r d y))
        (liftChartAmplitude r d (chartAuxiliaryAmplitude r d ν hf) (chartAuxiliaryCosphere r d y))
    rw [show liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r d y) = _ from hR,
      liftChartAuxiliaryInverse_apply, liftChartAmplitude_apply, liftChartAmplitude_apply]
    exact auxiliaryTraceLinear_roundOverlap r q d z (chartAuxiliaryAmplitude r d ν hf y)
  rw [hμ]
  apply hφ.ae_map_iff.mpr
  exact (withDensity_absolutelyContinuous ((traceMeasure ν).restrict U) (chartInverseCutoffSquare d)).ae_le
    ((ae_restrict_mem (μ := traceMeasure ν) hU).mono hpt)

variable [SecondCountableTopology M]

/-- On a compact part of a genuine chart overlap, the two intrinsic auxiliary
trace controls of the same original sequence and subsequence coincide. The
trace-normalized amplitude matrices coincide there after the actual receiving
frame change. -/
theorem original_compactOverlap_amplitudeTraceControls_agree
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hbnd : AuxiliaryAdmissibility.CompactDhBound r B g)
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
    let W := amplitudeCosphereWindow r K
    let τq := (chartAmplitudeTraceControl r q νq hfq).restrict W
    let τd := (chartAmplitudeTraceControl r d νd hfd).restrict W
    let A := liftChartAmplitude r q (chartAuxiliaryAmplitude r q νq hfq)
    let D := liftChartAmplitude r d (fun z i j => transportedAmplitudeEntry r q d νd hfd i j z)
    τq = τd ∧
      (fun p => (chartAmplitudeTraceWeight r q νq hfq p)⁻¹ • A p)
        =ᵐ[τq] fun p => (chartAmplitudeTraceWeight r d νd hfd p)⁻¹ • D p := by
  intro W τq τd A D
  let μq := (chartCosphereControlMeasure r q νq).restrict W
  let μd := (chartCosphereControlMeasure r d νd).restrict W
  let R := liftChartAuxiliaryInverse r q
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  obtain ⟨hFq, hFd, _, _, hEq⟩ := original_compactOverlap_amplitudeDensities_on_sum r B g
    hB hg hsB hsG hnB hnG hconv hbnd hv σ hσ q d νq hfq νd hfd hRq hRd hK hSub
  letI : IsFiniteMeasure μq := hFq
  letI : IsFiniteMeasure μd := hFd
  have hA (i j : Pair) : Measurable (fun p => A p i j) :=
    measurable_liftChartAmplitude_entry r q _ i j (measurable_chartAuxiliaryAmplitude_entry r q νq hfq i j)
  have hD (i j : Pair) : Measurable (fun p => D p i j) :=
    measurable_liftChartAmplitude_entry r d _ i j (measurable_transportedAmplitudeEntry r q d νd hfd i j)
  have htrace := chartAmplitudeTraceWeight_ae_of_transport r q d νd hfd hK.isClosed.measurableSet
    (hSub.trans inter_subset_left)
  obtain ⟨hCtrl, hNorm⟩ := normalization_agrees_on_common_auxiliary_control μq μd R A D
    (fun i j => (measurable_liftChartAuxiliaryInverse_entry r q i j).aemeasurable)
    (fun i j => (hA i j).aemeasurable) (fun i j => (hD i j).aemeasurable) hEq
  have hτq : τq = μq.withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q νq hfq p)) := by
    change ((chartCosphereControlMeasure r q νq).withDensity _).restrict W = _
    rw [restrict_withDensity hW]
  have hτd : τd = μd.withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r d νd hfd p)) := by
    change ((chartCosphereControlMeasure r d νd).withDensity _).restrict W = _
    rw [restrict_withDensity hW]
  have hCtrlEq : τq = τd := hτq.trans <|
    hCtrl.trans ((withDensity_congr_ae (htrace.fun_comp ENNReal.ofReal)).trans hτd.symm)
  have hAC : τq ≪ μd := hCtrlEq.symm ▸ (hτd.symm ▸ withDensity_absolutelyContinuous _ _)
  have hTraceq : (fun p => auxiliaryTraceLinear (R p) (D p))
      =ᵐ[τq] chartAmplitudeTraceWeight r d νd hfd := hAC.ae_eq htrace
  have hEqTrace : (fun p => (auxiliaryTraceLinear (R p) (D p))⁻¹ • D p)
      =ᵐ[τq] fun p => (chartAmplitudeTraceWeight r d νd hfd p)⁻¹ • D p := by
    filter_upwards [hTraceq] with p hp
    rw [hp]
  have hNorm' : (fun p => (chartAmplitudeTraceWeight r q νq hfq p)⁻¹ • A p)
      =ᵐ[τq] fun p => (auxiliaryTraceLinear (R p) (D p))⁻¹ • D p := by
    rw [hτq]
    exact hNorm
  exact ⟨hCtrlEq, hNorm'.trans hEqTrace⟩

end Burnett.Microlocal.Overlap
