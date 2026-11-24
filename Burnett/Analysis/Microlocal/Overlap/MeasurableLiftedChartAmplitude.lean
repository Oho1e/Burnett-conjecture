import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeTraceLift
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option maxRecDepth 2500

noncomputable section
namespace Burnett.Microlocal.Overlap

open Set MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ChartVolume
open Burnett.Geometry.MetricJetNaturality (derivativeMatrix_apply)
open Burnett.Geometry.UnitCosphere (Cosphere)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F05.OriginalVolumeAuxiliaryAmplitude (chartAuxiliaryAmplitude)
open Burnett.F05.OverlapCovectors (tensorPairTransition)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot Pair auxiliaryAmplitudeCovariance
  measurable_auxiliaryAmplitudeCovariance_entry)
open Burnett.Microlocal.FixedChartGeometricDensity (auxiliaryUnitCovector chartPhysicalCovariance roundCovector)
open Burnett.Microlocal.MatrixMeasureAssembly (entryMeasure traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density)
open Burnett.Microlocal.OverlapGradient (overlapTransition_measurable)
open scoped ContDiff Manifold Matrix ComplexConjugate

open private continuous_auxiliaryUnitCovector from Burnett.Analysis.Microlocal.ChartAmplitudeMeasure

private theorem measurable_extend_matrix_entry {X Y I K E : Type*} [MeasurableSpace X]
    [MeasurableSpace Y] [MeasurableSpace E] [Zero E] {φ : X → Y} (hφ : MeasurableEmbedding φ)
    (F : X → Matrix I K E) (i : I) (j : K) (hF : Measurable (fun x => F x i j)) :
    Measurable (fun y => Function.extend φ F (fun _ => 0) y i j) := by
  classical
  have he : (fun y => Function.extend φ F (fun _ => 0) y i j) =
      Function.extend φ (fun x => F x i j) (fun _ => 0) := by
    funext y
    by_cases hy : y ∈ range φ
    · obtain ⟨x, rfl⟩ := hy
      simp only [hφ.injective.extend_apply]
    · rw [Function.extend_apply' F (fun _ => 0) y hy,
        Function.extend_apply' (fun x => F x i j) (fun _ => 0) y hy]
      rfl
  rw [he]
  exact hφ.measurable_extend hF measurable_const

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The original unit-chart amplitude has Borel measurable entries on the whole
round chart. In particular no modification of its density on null sets is needed
before comparing it on a sum of two reference measures. -/
theorem measurable_chartAuxiliaryAmplitude_entry
    (r : Metric (M := M)) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (i j : Pair) : Measurable (fun z => chartAuxiliaryAmplitude r q ν hf z i j) := by
  let R := chartAuxiliaryInverse r q
  have hR (a b : Index) : Continuous (fun y => R y a b) :=
    (continuous_apply b).comp ((continuous_apply a).comp (continuous_chartAuxiliaryInverse r q))
  have hM (k l : JetSlot) :
      Measurable (fun z => chartPhysicalCovariance q.ball ν hf z k l) := by
    let c := entryMeasure ν hf l k
    let μ := traceMeasure ν
    change Measurable (fun z => c.rnDeriv μ z)
    have hre := Complex.measurable_ofReal.comp (SignedMeasure.measurable_rnDeriv c.re μ)
    have him := Complex.measurable_ofReal.comp (SignedMeasure.measurable_rnDeriv c.im μ)
    have h : Measurable (fun z => (c.re.rnDeriv μ z : ℂ) + (c.im.rnDeriv μ z : ℂ) * Complex.I) :=
      hre.add (him.mul measurable_const)
    simpa only [show (fun z => (c.re.rnDeriv μ z : ℂ) + (c.im.rnDeriv μ z : ℂ) * Complex.I) =
      c.rnDeriv μ from funext fun z => Complex.re_add_im (c.rnDeriv μ z)] using h
  exact measurable_auxiliaryAmplitudeCovariance_entry (fun z : Chart q.ball => R z.1)
    (fun z => auxiliaryUnitCovector (R z.1) (roundCovector z))
    (chartPhysicalCovariance q.ball ν hf) (fun a b => ((hR a b).comp continuous_fst).measurable)
    (fun a => (continuous_auxiliaryUnitCovector q.ball R hR (chartAuxiliaryNorm_pos r q) a).measurable)
    hM i j

omit [IsManifold Model ∞ M] in
private theorem measurable_receivingToSourceCotangent_entry
    (q d : CompactChartInput M) (i j : Index) :
    Measurable (fun y => receivingToSourceCotangent q d y i j) := by
  let e : CoordinateSpace → CoordinateSpace := chartTransition q.center d.center
  have h := measurable_fderiv_apply_const ℝ e (coordinateBasis i)
  simpa only [receivingToSourceCotangent, Matrix.transpose_apply, derivativeMatrix_apply] using
    (EuclideanSpace.proj (𝕜 := ℝ) j).continuous.measurable.comp
      (h.comp (overlapTransition_measurable d.center q.center))

/-- The actual receiving-to-source congruence preserves entrywise Borel measurability. -/
theorem measurable_transportedAmplitudeEntry
    (r : Metric (M := M)) (q d : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart d.ball)) (hf : ∀ v, IsFiniteMeasure (ν v))
    (u v : Pair) : Measurable (transportedAmplitudeEntry r q d ν hf u v) := by
  let T (z : Chart d.ball) := receivingToSourceCotangent q d z.1
  let D (z : Chart d.ball) := tensorPairTransition (T z)
  let A := chartAuxiliaryAmplitude r d ν hf
  have hT (a b : Index) : Measurable (fun z => T z a b) :=
    (measurable_receivingToSourceCotangent_entry q d a b).comp
      (continuous_subtype_val.comp continuous_fst).measurable
  have hD (i j : Pair) : Measurable (fun z => D z i j) := by
    simp only [D, tensorPairTransition, Matrix.kroneckerMap_apply, Matrix.map_apply]
    exact (Complex.measurable_ofReal.comp (hT i.1 j.1)).mul
      (Complex.measurable_ofReal.comp (hT i.2 j.2))
  have hA (i j : Pair) : Measurable (fun z => A z i j) :=
    measurable_chartAuxiliaryAmplitude_entry r d ν hf i j
  change Measurable (fun z => (D z * A z * (D z)ᴴ) u v)
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  exact Finset.measurable_sum _ fun k _ =>
    (Finset.measurable_sum _ fun l _ => (hD u l).mul (hA l k)).mul
      (Complex.continuous_conj.measurable.comp (hD v k))

variable [T2Space M]

/-- Entrywise measurability is preserved by inverse chart extension to the
actual auxiliary cosphere. -/
theorem measurable_liftChartAmplitude_entry (r : Metric (M := M)) (q : CompactChartInput M)
    (F : Chart q.ball → Matrix Pair Pair ℂ) (i j : Pair)
    (hF : Measurable (fun z => F z i j)) :
    Measurable (fun p => liftChartAmplitude r q F p i j) :=
  measurable_extend_matrix_entry (measurableEmbedding_chartAuxiliaryCosphere r q) F i j hF

/-- Inverse auxiliary metric entries in the chosen chart frame on the unit
cosphere, extended by zero outside the chart image. -/
def liftChartAuxiliaryInverse (r : Metric (M := M)) (q : CompactChartInput M) :
    Cosphere r → Tensor2 :=
  Function.extend (chartAuxiliaryCosphere r q) (fun z => chartAuxiliaryInverse r q z.1) (fun _ => 0)

theorem liftChartAuxiliaryInverse_apply (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) :
    liftChartAuxiliaryInverse r q (chartAuxiliaryCosphere r q z) = chartAuxiliaryInverse r q z.1 :=
  (measurableEmbedding_chartAuxiliaryCosphere r q).injective.extend_apply _ _ _

theorem measurable_liftChartAuxiliaryInverse_entry (r : Metric (M := M)) (q : CompactChartInput M)
    (i j : Index) : Measurable (fun p => liftChartAuxiliaryInverse r q p i j) :=
  measurable_extend_matrix_entry (measurableEmbedding_chartAuxiliaryCosphere r q)
    (fun z => chartAuxiliaryInverse r q z.1) i j
    (((continuous_apply j).comp ((continuous_apply i).comp
      ((continuous_chartAuxiliaryInverse r q).comp continuous_fst))).measurable)

end Burnett.Microlocal.Overlap
