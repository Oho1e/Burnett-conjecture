import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitude
import Burnett.Analysis.Microlocal.Overlap.CompactChartTraceNormalization
import Burnett.Analysis.Microlocal.Overlap.ChartTraceNormalizedAmplitudeKernel

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 1800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Matrix Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.ContravariantTensor (tensorTangentBasis_apply)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeCovarianceDensity chartComponents chartComponents_chartAmplitude chartTangentBasis
    chartTangentBasis_preferred components components_apply)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector roundCovector)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open Burnett.F07.IntrinsicAmplitude
  (auxiliaryTraceLinear chartAmplitudeTangentBasis intrinsicAuxiliaryTrace
    intrinsicAuxiliaryTrace_eq_chart orderedChartAmplitudeComponents)
open scoped ContDiff Manifold Matrix ComplexOrder

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Both formulas evaluate the four ordered slots on the actual chart tangent basis. -/
theorem orderedChartAmplitudeComponents_eq_chartComponents
    (r : Metric (M := M)) (q : CompactChartInput M) (J : AmplitudeCovarianceDensity r)
    (z : Chart q.ball)
    (hx : projection (chartAuxiliaryCosphere r q z) ∈ (chartAt CoordinateSpace q.center).source) :
    orderedChartAmplitudeComponents r q J z =
      chartComponents (.atPoint q.center) (projection (chartAuxiliaryCosphere r q z)) hx
        (J (chartAuxiliaryCosphere r q z)) := by
  let p := chartAuxiliaryCosphere r q z
  let x := projection p
  have hb : chartTangentBasis (.atPoint q.center) x hx = chartAmplitudeTangentBasis r q z := by
    apply Module.Basis.eq_of_apply_eq
    intro i
    rw [chartTangentBasis_preferred]
    exact (tensorTangentBasis_apply q.center x hx i).symm
  ext i j
  change J p ![chartAmplitudeTangentBasis r q z i.1, chartAmplitudeTangentBasis r q z i.2,
    chartAmplitudeTangentBasis r q z j.1, chartAmplitudeTangentBasis r q z j.2] =
      components (chartTangentBasis (.atPoint q.center) x hx) (J p) i j
  rw [components_apply]
  exact congrArg (fun b : Module.Basis Index ℝ (TangentSpace Model x) =>
    J p ![b i.1, b i.2, b j.1, b j.2]) hb.symm

variable [T2Space M]

/-- Recover the actual chart entries at any chart point where the two four-slot tensors agree. -/
theorem orderedChartAmplitudeComponents_eq_original_of_density_eq
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (J : AmplitudeCovarianceDensity r) (z : Chart q.ball)
    (hJ : J (chartAuxiliaryCosphere r q z) =
      chartNormalizedIntrinsicAmplitude r q ν hf (chartAuxiliaryCosphere r q z)) :
    orderedChartAmplitudeComponents r q J z =
      (chartAmplitudeTraceWeight r q ν hf (chartAuxiliaryCosphere r q z))⁻¹ •
        chartAuxiliaryAmplitude r q ν hf z := by
  let p := chartAuxiliaryCosphere r q z
  have hx : projection p ∈ (chartAt CoordinateSpace q.center).source :=
    (chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property)
  rw [orderedChartAmplitudeComponents_eq_chartComponents r q J z hx, hJ,
    chartNormalizedIntrinsicAmplitude_of_mem r q ν hf p hx, chartComponents_chartAmplitude,
    liftChartAmplitude_apply]

variable [MeasurableSpace M] [BorelSpace M]

/-- The glued field recovers the ordered original normalized entries in the same represented chart. -/
theorem HasOriginalAmplitudeChartLaws.ae_orderedChartComponents
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hnB : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r}
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      ∃ z ∈ amplitudeChartWindow r q K, chartAuxiliaryCosphere r q z = p ∧
        orderedChartAmplitudeComponents r q A.density z =
          (chartAmplitudeTraceWeight r q ν hf p)⁻¹ • chartAuxiliaryAmplitude r q ν hf z := by
  obtain ⟨hControl, hField⟩ := hA q ν hf hRep K hK hSub
  rw [hControl]
  have hPoints := ae_chartAmplitudeTraceControl_restrict_exists_windowPoint r q ν hf hK.isClosed.measurableSet
  filter_upwards [hField, hPoints] with p hp hPoint
  obtain ⟨z, hz, rfl⟩ := hPoint
  exact ⟨z, hz, rfl, orderedChartAmplitudeComponents_eq_original_of_density_eq r q ν hf A.density z hp⟩

variable [SecondCountableTopology M]

/-- On a compact part of a represented chart, the global four-slot density has
the original positive normalized covariance and Ricci kernel at the same actual point. -/
theorem HasOriginalAmplitudeChartLaws.ae_positive_unitTrace_ricciKernel
    {r : Metric (M := M)} {B : Field (M := M)} {g : ℕ → Field (M := M)}
    {hB : IsSmooth B} {hg : ∀ n, IsSmooth (g n)} {hnB : IsNondegenerate B}
    {σ : ℕ → ℕ} {A : IntrinsicAmplitudeCovariance r}
    (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n)) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (hσ : StrictMono σ)
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    ∀ᵐ p ∂A.control.restrict (amplitudeCosphereWindow r K),
      ∃ z ∈ amplitudeChartWindow r q K, chartAuxiliaryCosphere r q z = p ∧
        let C := orderedChartAmplitudeComponents r q A.density z
        C = (chartAmplitudeTraceWeight r q ν hf p)⁻¹ • chartAuxiliaryAmplitude r q ν hf z ∧
        C.PosSemidef ∧ auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) C = 1 ∧
        intrinsicAuxiliaryTrace r A.density p = 1 ∧
        ∀ v : Pair → ℂ,
          let k (a b : Index) := (C *ᵥ v) (a, b)
          let η := auxiliaryUnitCovector (chartAuxiliaryInverse r q z.1) (roundCovector z)
          IsSymmetricComplexTensor k ∧
            ∀ a b, complexRicciSymbol (backgroundInverse B q.center z.1) η k a b = 0 := by
  obtain ⟨hControl, hField⟩ := hA q ν hf hRep K hK hSub
  rw [hControl]
  have hPos := (original_compactChart_traceNormalizedAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ q ν hf hRep hK hSub).1
  have hKernel := original_chart_traceNormalizedAmplitude_ae_ricciKernel r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ q ν hf hRep hK.isClosed.measurableSet
  filter_upwards [hField, hPos, hKernel] with p hp hPosAt hKernelAt
  obtain ⟨z, hz, rfl, hRicci⟩ := hKernelAt
  let p := chartAuxiliaryCosphere r q z
  let C := orderedChartAmplitudeComponents r q A.density z
  let D := (chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
    liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p
  have hC := orderedChartAmplitudeComponents_eq_original_of_density_eq r q ν hf A.density z hp
  have hCD : C = D := hC.trans (by
    change _ = (chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
      liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) (chartAuxiliaryCosphere r q z)
    rw [liftChartAmplitude_apply])
  have hPosC : C.PosSemidef := hCD ▸ hPosAt.1
  have hTrace : auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) C = 1 := by
    rw [hCD, ← liftChartAuxiliaryInverse_apply r q z]
    exact hPosAt.2
  refine ⟨z, hz, rfl, hC, hPosC, hTrace, ?_, ?_⟩
  · exact (intrinsicAuxiliaryTrace_eq_chart r q A.density z).trans hTrace
  · rw [show orderedChartAmplitudeComponents r q A.density z = D from hCD]
    exact hRicci

end Burnett.Microlocal.Overlap
