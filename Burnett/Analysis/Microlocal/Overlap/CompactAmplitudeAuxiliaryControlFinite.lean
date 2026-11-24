import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliaryControl

set_option autoImplicit false
set_option maxRecDepth 2800
set_option maxHeartbeats 950000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.F07.IntrinsicAmplitude (auxiliaryTraceLinear auxiliaryTraceLinear_apply)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M]

private theorem norm_liftChartAuxiliaryInverse_entry_bounded
    (r : Metric (M := M)) (q : CompactChartInput M) (i j : Index) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : Cosphere r, ‖liftChartAuxiliaryInverse r q p i j‖ ≤ C := by
  let f (z : Chart q.ball) := chartAuxiliaryInverse r q z.1 i j
  have hf : Continuous f :=
    (continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_chartAuxiliaryInverse r q).comp continuous_fst))
  obtain ⟨C, hC⟩ := (isCompact_range hf).isBounded.exists_norm_le
  refine ⟨max C 0, le_max_right _ _, fun p => ?_⟩
  by_cases hp : ∃ z, chartAuxiliaryCosphere r q z = p
  · obtain ⟨z, rfl⟩ := hp
    rw [liftChartAuxiliaryInverse_apply]
    exact (hC (f z) (mem_range_self z)).trans (le_max_left _ _)
  · rw [liftChartAuxiliaryInverse, Function.extend_apply' _ _ _ hp]
    change ‖(0 : ℝ)‖ ≤ max C 0
    rw [norm_zero]
    exact le_max_right C 0

variable [MeasurableSpace M] [BorelSpace M]

/-- On a compact base set contained in a nonzero chart locus, the auxiliary
trace control is finite. This uses the same cutoff-normalized chart entries
and the actual inverse metric on the compact round chart. -/
theorem chartAmplitudeTraceControl_lt_top_on_compact
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    chartAmplitudeTraceControl r q ν hf (amplitudeCosphereWindow r K) < ⊤ := by
  let W := amplitudeCosphereWindow r K
  let μ := (chartCosphereControlMeasure r q ν).restrict W
  let A := liftChartAmplitude r q (chartAuxiliaryAmplitude r q ν hf)
  let R := liftChartAuxiliaryInverse r q
  have hW : MeasurableSet W := measurableSet_amplitudeCosphereWindow r hK.isClosed.measurableSet
  have hA (i j : Pair) : Integrable (fun p => A p i j) μ :=
    (normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude r q ν (chartAuxiliaryAmplitude r q ν hf)
      hK.isClosed.measurableSet i j
      (integrable_normalizedCosphereAmplitudeEntry_on_compact r q ν hf i j hK hSub)).1
  choose C hC hBound using norm_liftChartAuxiliaryInverse_entry_bounded r q
  have hTerm (i j : Pair) : Integrable (fun p => (R p i.1 j.1 * R p i.2 j.2) * (A p i j).re) μ := by
    have hMeas (a b : Index) : Measurable (fun p => R p a b) :=
      measurable_liftChartAuxiliaryInverse_entry r q a b
    refine ((hA i j).re).bdd_mul ((hMeas i.1 j.1).mul (hMeas i.2 j.2)).aestronglyMeasurable
      ⟨C i.1 j.1 * C i.2 j.2, fun p => ?_⟩
    rw [norm_mul]
    exact mul_le_mul (hBound i.1 j.1 p) (hBound i.2 j.2 p) (norm_nonneg _) (hC i.1 j.1)
  have hInt : Integrable (chartAmplitudeTraceWeight r q ν hf) μ := by
    change Integrable (fun p => auxiliaryTraceLinear (R p) (A p)) μ
    simp only [auxiliaryTraceLinear_apply]
    exact integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => hTerm i j
  letI : IsFiniteMeasure (μ.withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p))) :=
    isFiniteMeasure_withDensity_ofReal hInt.hasFiniteIntegral
  have hEq : (chartAmplitudeTraceControl r q ν hf).restrict W =
      μ.withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p)) := by
    rw [chartAmplitudeTraceControl, restrict_withDensity hW]
  have hFin := measure_lt_top (μ.withDensity (fun p => ENNReal.ofReal (chartAmplitudeTraceWeight r q ν hf p))) univ
  rwa [← hEq, Measure.restrict_apply_univ] at hFin

end Burnett.Microlocal.Overlap
