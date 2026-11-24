import Burnett.Analysis.Microlocal.Overlap.ChartCosphereControlMeasure
import Burnett.Analysis.Microlocal.Overlap.NormalizedAmplitudeOverlap

set_option autoImplicit false
set_option maxRecDepth 2500

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry
open ConnectionDifference ManifoldMetric
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot Pair)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (traceMeasure_isFinite)
open Burnett.X02.SobolevTestJet (test_smooth)
open scoped ContDiff Manifold ENNReal

open private isCompact_amplitudeChartWindow continuousOn_chartInverseCutoffComplexSquare from
  Burnett.Analysis.Microlocal.Overlap.NormalizedAmplitudeOverlap

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Chart-frame matrix coefficients pulled back by the inverse of the actual
oriented auxiliary chart embedding, with zero extension outside its image. -/
def liftChartAmplitude (r : Metric (M := M)) (q : CompactChartInput M)
    (F : Chart q.ball → Matrix Pair Pair ℂ) : Cosphere r → Matrix Pair Pair ℂ :=
  Function.extend (chartAuxiliaryCosphere r q) F (fun _ => 0)

theorem liftChartAmplitude_apply [T2Space M] (r : Metric (M := M)) (q : CompactChartInput M)
    (F : Chart q.ball → Matrix Pair Pair ℂ) (z : Chart q.ball) :
    liftChartAmplitude r q F (chartAuxiliaryCosphere r q z) = F z :=
  (measurableEmbedding_chartAuxiliaryCosphere r q).injective.extend_apply _ _ _

omit [IsManifold Model ∞ M] in
private theorem measurable_chartInverseCutoffSquare (q : CompactChartInput M) :
    Measurable (chartInverseCutoffSquare q) :=
  ENNReal.measurable_ofReal.comp
    ((((test_smooth q.cutoff).continuous.measurable.comp continuous_subtype_val.measurable).comp
      continuous_fst.measurable).inv.pow_const 2)

omit [IsManifold Model ∞ M] in
private theorem chartInverseCutoffSquare_toReal_smul (q : CompactChartInput M)
    (z : Chart q.ball) (a : ℂ) :
    (chartInverseCutoffSquare q z).toReal • a = chartInverseCutoffComplexSquare q z * a := by
  rw [chartInverseCutoffSquare, ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  rfl

variable [MeasurableSpace M] [BorelSpace M]

/-- Restriction to a base window commutes with the actual weighted chart pushforward. -/
theorem chartCosphereControlMeasure_restrict
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) {K : Set M} (hK : MeasurableSet K) :
    (chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K) =
      (((traceMeasure ν).restrict (amplitudeChartWindow r q K)).withDensity
        (chartInverseCutoffSquare q)).map (chartAuxiliaryCosphere r q) := by
  have hW := measurableSet_amplitudeCosphereWindow r hK
  have hφ := (continuous_chartAuxiliaryCosphere r q).measurable
  rw [chartCosphereControlMeasure, Measure.restrict_map hφ hW, restrict_withDensity (hφ hW)]
  rfl

variable [T2Space M]

/-- The reciprocal cutoff is bounded on the lift of a compact base set inside
the nonzero chart locus, so its weighted original trace is finite there. -/
theorem isFiniteMeasure_chartCosphereControlMeasure_restrict_compact
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    {K : Set M} (hK : IsCompact K) (hSub : K ⊆ q.nonzeroLocus) :
    IsFiniteMeasure ((chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K)) := by
  let U := amplitudeChartWindow r q K
  let μ := (traceMeasure ν).restrict U
  letI : IsFiniteMeasure (traceMeasure ν) := traceMeasure_isFinite ν hf
  letI : IsFiniteMeasure μ := inferInstanceAs (IsFiniteMeasure ((traceMeasure ν).restrict U))
  have hU : MeasurableSet U := measurableSet_amplitudeChartWindow r q hK.isClosed.measurableSet
  obtain ⟨C, hC⟩ := ((isCompact_amplitudeChartWindow r q hK).image_of_continuousOn
    (continuousOn_chartInverseCutoffComplexSquare r q hSub)).isBounded.exists_norm_le
  have hbound : chartInverseCutoffSquare q ≤ᵐ[μ] fun _ => ENNReal.ofReal C := by
    filter_upwards [ae_restrict_mem (μ := traceMeasure ν) hU] with z hz
    apply ENNReal.ofReal_le_ofReal
    simpa only [chartInverseCutoffComplexSquare, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (((q.cutoff : CoordinateSpace → ℝ) z.1)⁻¹))] using
      hC _ (mem_image_of_mem (chartInverseCutoffComplexSquare q) hz)
  letI : IsFiniteMeasure (μ.withDensity (chartInverseCutoffSquare q)) := by
    constructor
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    exact (lintegral_mono_ae hbound).trans_lt (by
      rw [lintegral_const]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ univ))
  rw [chartCosphereControlMeasure_restrict r q ν hK.isClosed.measurableSet]
  exact Measure.isFiniteMeasure_map (μ.withDensity _) (chartAuxiliaryCosphere r q)

/-- Absorb the real reciprocal square into the positive trace and move the
complex entry to the unit cosphere as a density with respect to that trace. -/
theorem normalizedCosphereChartEntryOn_eq_withDensity_liftChartAmplitude
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (F : Chart q.ball → Matrix Pair Pair ℂ)
    {K : Set M} (hK : MeasurableSet K) (i j : Pair)
    (hI : Integrable (fun z => chartInverseCutoffComplexSquare q z * F z i j)
      ((traceMeasure ν).restrict (amplitudeChartWindow r q K))) :
    let τ := (chartCosphereControlMeasure r q ν).restrict (amplitudeCosphereWindow r K)
    let f : Cosphere r → ℂ := fun p => liftChartAmplitude r q F p i j
    Integrable f τ ∧ normalizedCosphereChartEntryOn r q (traceMeasure ν) (fun z => F z i j) K =
      τ.withDensityᵥ f := by
  intro τ f
  let φ := chartAuxiliaryCosphere r q
  let μ := (traceMeasure ν).restrict (amplitudeChartWindow r q K)
  let w := chartInverseCutoffSquare q
  let κ := μ.withDensity w
  have hφ : MeasurableEmbedding φ := measurableEmbedding_chartAuxiliaryCosphere r q
  have hτ : τ = κ.map φ := chartCosphereControlMeasure_restrict r q ν hK
  have hw : Measurable w := measurable_chartInverseCutoffSquare q
  have hwfin (z : Chart q.ball) : w z < ⊤ := ENNReal.ofReal_lt_top
  have hf : f ∘ φ = fun z => F z i j := by
    funext z
    simp only [Function.comp_apply, f, φ, liftChartAmplitude_apply]
  have hInt : Integrable (fun z => F z i j) κ := by
    apply (integrable_withDensity_iff_integrable_smul' hw (Filter.Eventually.of_forall hwfin)).mpr
    simpa only [w, chartInverseCutoffSquare_toReal_smul] using hI
  have hPush : Integrable f (κ.map φ) := hφ.integrable_map_iff.mpr (hf.symm ▸ hInt)
  rw [hτ]
  refine ⟨hPush, ?_⟩
  ext S hS
  change ((μ.withDensityᵥ (fun z => chartInverseCutoffComplexSquare q z * F z i j)).map φ) S =
    ((κ.map φ).withDensityᵥ f) S
  rw [VectorMeasure.map_apply _ hφ.measurable hS, withDensityᵥ_apply hI (hφ.measurable hS),
    withDensityᵥ_apply hPush hS, hφ.setIntegral_map]
  change (∫ z in φ ⁻¹' S, chartInverseCutoffComplexSquare q z * F z i j ∂μ) =
    ∫ z in φ ⁻¹' S, (f ∘ φ) z ∂κ
  rw [hf, setIntegral_withDensity_eq_setIntegral_toReal_smul hw
    (Filter.Eventually.of_forall hwfin) _ (hφ.measurable hS)]
  simp only [w, chartInverseCutoffSquare_toReal_smul]

end Burnett.Microlocal.Overlap
