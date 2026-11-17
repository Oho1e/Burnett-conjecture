import Burnett.Geometry.RiemannianVolume
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-!
# Coordinate volume under actual chart changes

The metric pullback is the covariant matrix expression A.transpose * R * A,
with columns recording input-coordinate basis vectors and rows recording the
output coordinates. The sqrt(det R) density transformation is proved from
this expression. The weighted-measure pushforward is then proved by the
Jacobian theorem, including for a genuine chartAt overlap on a C1 manifold.

These are local coordinate overlap statements. They do not construct or
identify a global measure on the manifold. No density or measure equality
is an input to the actual-pullback versions.
-/

noncomputable section

namespace Burnett.Geometry.ChartVolume

open MeasureTheory Matrix Set
open scoped ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.RiemannianVolume

/-- The matrix of a genuine Frechet derivative in the fixed coordinate basis. -/
def derivativeMatrix (L : CoordinateSpace →L[ℝ] CoordinateSpace) : Matrix Index Index ℝ :=
  LinearMap.toMatrix coordinateBasis coordinateBasis L.toLinearMap

theorem det_derivativeMatrix (L : CoordinateSpace →L[ℝ] CoordinateSpace) :
    (derivativeMatrix L).det = L.det :=
  LinearMap.det_toMatrix coordinateBasis L.toLinearMap

/-- Covariant congruence has two determinant factors. No positivity is required. -/
theorem det_pullback (R A : Matrix Index Index ℝ) :
    (A.transpose * R * A).det = A.det ^ 2 * R.det := by
  simp only [Matrix.det_mul, Matrix.det_transpose]
  ring

theorem sqrt_det_pullback (R A : Matrix Index Index ℝ) :
    Real.sqrt (A.transpose * R * A).det = |A.det| * Real.sqrt R.det := by
  rw [det_pullback, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem rho_pullback (R : CoordinateSpace → Matrix Index Index ℝ)
    (φ : CoordinateSpace → CoordinateSpace)
    (J : CoordinateSpace → CoordinateSpace →L[ℝ] CoordinateSpace) (x : CoordinateSpace) :
    rho (fun y => (derivativeMatrix (J y)).transpose * R (φ y) * derivativeMatrix (J y)) x =
      ENNReal.ofReal |(J x).det| * rho R (φ x) := by
  simp only [rho, sqrt_det_pullback, det_derivativeMatrix,
    ENNReal.ofReal_mul (abs_nonneg _)]

/-- The source metric is the actual computed pullback, rather than an assumed
volume-density transformation. Differentiability and injectivity are local to s. -/
theorem map_pullback_coordinateMeasure_restrict
    (R : CoordinateSpace → Matrix Index Index ℝ)
    (φ : CoordinateSpace → CoordinateSpace)
    (J : CoordinateSpace → CoordinateSpace →L[ℝ] CoordinateSpace)
    (s : Set CoordinateSpace) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivWithinAt φ (J x) s x) (hi : InjOn φ s) :
    Measure.map φ ((coordinateMeasure
      (fun y => (derivativeMatrix (J y)).transpose * R (φ y) * derivativeMatrix (J y))).restrict s) =
      (coordinateMeasure R).restrict (φ '' s) := by
  have him : MeasurableSet (φ '' s) := measurable_image_of_fderivWithin hs hφ hi
  have hmeas : AEMeasurable φ (volume.restrict s) :=
    (show ContinuousOn φ s from fun x hx => (hφ x hx).continuousWithinAt).aemeasurable hs
  let w := fun y => rho
    (fun z => (derivativeMatrix (J z)).transpose * R (φ z) * derivativeMatrix (J z)) y
  have hwmeas : AEMeasurable φ ((volume.restrict s).withDensity w) :=
    hmeas.mono_ac (withDensity_absolutelyContinuous _ _)
  simp only [coordinateMeasure, restrict_withDensity hs, restrict_withDensity him]
  apply Measure.ext fun t ht => ?_
  have hpre : NullMeasurableSet (φ ⁻¹' t) (volume.restrict s) :=
    hmeas.nullMeasurableSet_preimage ht
  rw [Measure.map_apply_of_aemeasurable hwmeas ht,
    withDensity_apply₀ _ hpre, withDensity_apply _ ht,
    ← lintegral_indicator ht, lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs hφ hi]
  rw [← lintegral_indicator₀ hpre]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem hs] with x hx
  by_cases hxt : φ x ∈ t
  · simp only [mem_preimage, hxt, indicator_of_mem]
    exact rho_pullback R φ J x
  · simp only [mem_preimage, hxt, not_false_eq_true, indicator_of_notMem, mul_zero]

/-- Consumer for a metric component transformation established independently
from an underlying tensor field. The matrix identity is the only geometric input. -/
theorem map_coordinateMeasure_restrict_of_pullback
    (R S : CoordinateSpace → Matrix Index Index ℝ)
    (φ : CoordinateSpace → CoordinateSpace)
    (J : CoordinateSpace → CoordinateSpace →L[ℝ] CoordinateSpace)
    (s : Set CoordinateSpace) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivWithinAt φ (J x) s x) (hi : InjOn φ s)
    (hR : ∀ x ∈ s, S x = (derivativeMatrix (J x)).transpose * R (φ x) * derivativeMatrix (J x)) :
    Measure.map φ ((coordinateMeasure S).restrict s) =
      (coordinateMeasure R).restrict (φ '' s) := by
  have hS : (coordinateMeasure S).restrict s =
      (coordinateMeasure (fun x => (derivativeMatrix (J x)).transpose * R (φ x) *
        derivativeMatrix (J x))).restrict s := by
    simp only [coordinateMeasure, restrict_withDensity hs]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    simp only [rho, hR x hx]
  rw [hS]
  exact map_pullback_coordinateMeasure_restrict R φ J s hs hφ hi

/-- A genuine open partial homeomorphism with a C1 forward map supplies the
local derivative and injectivity inputs. No assumption on its extension outside
the source, or on the metric outside the target, is needed. -/
theorem map_openPartialHomeomorph_pullback_coordinateMeasure
    (R : CoordinateSpace → Matrix Index Index ℝ)
    (e : OpenPartialHomeomorph CoordinateSpace CoordinateSpace)
    (hc : ContDiffOn ℝ 1 e e.source) :
    Measure.map e ((coordinateMeasure (fun x =>
      (derivativeMatrix (fderiv ℝ e x)).transpose * R (e x) *
        derivativeMatrix (fderiv ℝ e x))).restrict e.source) =
      (coordinateMeasure R).restrict e.target := by
  have hd : DifferentiableOn ℝ e e.source := hc.differentiableOn le_rfl
  rw [← e.image_source_eq_target]
  apply map_pullback_coordinateMeasure_restrict R e (fderiv ℝ e) e.source e.open_source.measurableSet
  · intro x hx
    exact ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  · exact e.injOn

section Manifold

open scoped Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold (𝓘(ℝ, CoordinateSpace)) 1 M]

/-- The actual change from c-coordinates to d-coordinates, on the actual overlap. -/
def chartTransition (c d : M) : OpenPartialHomeomorph CoordinateSpace CoordinateSpace :=
  (chartAt CoordinateSpace c).symm.trans (chartAt CoordinateSpace d)

theorem contDiffOn_chartTransition (c d : M) :
    ContDiffOn ℝ 1 (chartTransition c d) (chartTransition c d).source := by
  have h : (chartAt CoordinateSpace c).symm.trans (chartAt CoordinateSpace d) ∈
      contDiffGroupoid 1 (𝓘(ℝ, CoordinateSpace)) :=
    HasGroupoid.compatible (chart_mem_atlas CoordinateSpace c) (chart_mem_atlas CoordinateSpace d)
  have h' := h.1
  change ContDiffOn ℝ 1 _ _ at h'
  simpa only [mfld_simps, chartTransition] using h'

/-- For genuine manifold charts, the atlas supplies C1 regularity; no
independently assumed derivative, Jacobian law, or measure equality remains. -/
theorem map_chartTransition_pullback_coordinateMeasure
    (R : CoordinateSpace → Matrix Index Index ℝ) (c d : M) :
    Measure.map (chartTransition c d) ((coordinateMeasure (fun x =>
      (derivativeMatrix (fderiv ℝ (chartTransition c d) x)).transpose *
        R (chartTransition c d x) *
        derivativeMatrix (fderiv ℝ (chartTransition c d) x))).restrict
          (chartTransition c d).source) =
      (coordinateMeasure R).restrict (chartTransition c d).target :=
  map_openPartialHomeomorph_pullback_coordinateMeasure R (chartTransition c d)
    (contDiffOn_chartTransition c d)

/-- This consumes the component transformation of one underlying metric in
two genuine charts. Only that tensor identity remains as geometric input. -/
theorem map_chartTransition_coordinateMeasure_of_pullback
    (R S : CoordinateSpace → Matrix Index Index ℝ) (c d : M)
    (hR : ∀ x ∈ (chartTransition c d).source,
      S x = (derivativeMatrix (fderiv ℝ (chartTransition c d) x)).transpose *
        R (chartTransition c d x) * derivativeMatrix (fderiv ℝ (chartTransition c d) x)) :
    Measure.map (chartTransition c d) ((coordinateMeasure S).restrict (chartTransition c d).source) =
      (coordinateMeasure R).restrict (chartTransition c d).target := by
  let e := chartTransition c d
  have hd : DifferentiableOn ℝ e e.source := (contDiffOn_chartTransition c d).differentiableOn le_rfl
  rw [← e.image_source_eq_target]
  apply map_coordinateMeasure_restrict_of_pullback R S e (fderiv ℝ e) e.source
    e.open_source.measurableSet _ e.injOn hR
  intro x hx
  exact ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt

end Manifold

end Burnett.Geometry.ChartVolume
