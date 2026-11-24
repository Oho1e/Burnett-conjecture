import Burnett.Analysis.Microlocal.Overlap.CompactChartTraceNormalization
import Burnett.Analysis.Microlocal.Overlap.GlobalIntrinsicAmplitude

set_option autoImplicit false
set_option maxRecDepth 2500
set_option maxHeartbeats 1500000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricSequence
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates
  (AmplitudeCovarianceDensity chartComponents chartComponents_chartAmplitude)
open Burnett.F05.ChartVolumeAmplitude (originalGradient_volumeWeightedL2)
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput RepresentsCompactJetPairings)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The ordered entries of the actual intrinsic amplitude in one preferred
chart. Integrals use the restriction to the chart's valid base window. -/
def intrinsicAmplitudeMatrix {r : Metric (M := M)} (c : M) (D : AmplitudeCovarianceDensity r)
    (p : Cosphere r) : Matrix Pair Pair ℂ := by
  classical
  exact if h : projection p ∈ (chartAt CoordinateSpace c).source then
    chartComponents (.atPoint c) (projection p) h (D p)
  else 0

theorem intrinsicAmplitudeMatrix_of_mem {r : Metric (M := M)} (c : M)
    (D : AmplitudeCovarianceDensity r) (p : Cosphere r)
    (hp : projection p ∈ (chartAt CoordinateSpace c).source) :
    intrinsicAmplitudeMatrix c D p = chartComponents (.atPoint c) (projection p) hp (D p) := by
  rw [intrinsicAmplitudeMatrix, dif_pos hp]

theorem intrinsicAmplitudeMatrix_chartNormalized_of_mem
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (p : Cosphere r) (hp : projection p ∈ (chartAt CoordinateSpace q.center).source) :
    intrinsicAmplitudeMatrix q.center (chartNormalizedIntrinsicAmplitude r q ν hf) p =
      (chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
        liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p := by
  rw [intrinsicAmplitudeMatrix_of_mem q.center _ p hp,
    chartNormalizedIntrinsicAmplitude_of_mem r q ν hf p hp, chartComponents_chartAmplitude]

variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]

/-- Every compact represented chart recovers the actual original complex entry
measure from the globally assembled intrinsic density and its one control. -/
theorem original_globalAmplitude_entryMeasure_on_compactChart
    (r : Metric (M := M)) (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (hsB : IsSymmetric B) (hsG : ∀ n, IsSymmetric (g n))
    (hnB : IsNondegenerate B) (hnG : ∀ n, IsNondegenerate (g n))
    (hconv : LocallyUniformlyConverges r g B) (hb : AuxiliaryAdmissibility.CompactDhBound r B g)
    (hv : ∀ n, IntrinsicRicciTrace.IsVacuum (g n)) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (A : IntrinsicAmplitudeCovariance r) (hA : HasOriginalAmplitudeChartLaws r B g hB hg hnB σ A)
    (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (hRep : RepresentsCompactJetPairings q.ball
      (originalGradient_volumeWeightedL2 B g hB hg hnB q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart)) σ ν hf)
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) (i j : Pair) :
    let τ := A.control.restrict (amplitudeCosphereWindow r K)
    let F (p : Cosphere r) := intrinsicAmplitudeMatrix q.center A.density p i j
    Integrable F τ ∧ τ.withDensityᵥ F = normalizedCosphereAmplitudeEntryOn r q ν hf i j K := by
  intro τ F
  let μq := chartAmplitudeTraceControl r q ν hf
  let τq := μq.restrict (amplitudeCosphereWindow r K)
  let D (p : Cosphere r) := (chartAmplitudeTraceWeight r q ν hf p)⁻¹ •
    liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf) p
  obtain ⟨hMeasure, hField⟩ := hA q ν hf hRep K hK hSub
  have hτ : τ = τq := hMeasure
  have hW := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hEq : F =ᵐ[τq] fun p => D p i j := by
    filter_upwards [hField, ae_restrict_mem (μ := μq) hW] with p hJ hp
    have hx : projection p ∈ (chartAt CoordinateSpace q.center).source := (hSub hp).1
    change intrinsicAmplitudeMatrix q.center A.density p i j = D p i j
    have hD : intrinsicAmplitudeMatrix q.center A.density p = D p := by
      rw [intrinsicAmplitudeMatrix_of_mem q.center A.density p hx, hJ,
        ← intrinsicAmplitudeMatrix_of_mem q.center _ p hx]
      exact intrinsicAmplitudeMatrix_chartNormalized_of_mem r q ν hf p hx
    exact congrFun (congrFun hD i) j
  have hLocal := (original_compactChart_traceNormalizedAmplitude r B g hB hg hsB hsG hnB hnG
    hconv hb hv σ hσ q ν hf hRep hK hSub).2 i j
  rw [hτ]
  exact ⟨hLocal.1.congr hEq.symm, (WithDensityᵥEq.congr_ae hEq).trans hLocal.2⟩

end Burnett.Microlocal.Overlap
