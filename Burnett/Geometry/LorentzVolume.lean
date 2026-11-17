import Burnett.Geometry.ChartVolume
import Burnett.Analysis.PositiveDensity

/-!
# The actual coordinate density sqrt(abs(det G))

This is the determinant density of a nondegenerate coordinate metric,
including a Lorentzian metric with negative determinant. It is distinct
from sqrt(det R) for the auxiliary positive metric. Global manifold
volume and the same-metric chart transformation remain separate inputs.
-/

noncomputable section

namespace Burnett.Geometry.LorentzVolume

open MeasureTheory Matrix Set
open scoped ENNReal
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ChartVolume

/-- The actual nonnegative absolute-determinant density. -/
def density {X : Type*} (G : X → Matrix Index Index ℝ) (x : X) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt |Matrix.det (G x)|)

/-- Coordinate Lebesgue volume weighted by the actual metric density. -/
def coordinateMeasure (G : CoordinateSpace → Matrix Index Index ℝ) : Measure CoordinateSpace :=
  volume.withDensity (density G)

theorem continuousOn_density {X : Type*} [TopologicalSpace X]
    (G : X → Matrix Index Index ℝ) (U : Set X) (hc : ContinuousOn G U) :
    ContinuousOn (density G) U := by
  have hd : ContinuousOn (fun x => Matrix.det (G x)) U := by
    intro x hx
    exact continuous_id.matrix_det.continuousAt.comp_continuousWithinAt (hc x hx)
  exact ENNReal.continuous_ofReal.comp_continuousOn hd.abs.sqrt

theorem aemeasurable_density_restrict {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) (G : X → Matrix Index Index ℝ)
    (U : Set X) (hU : MeasurableSet U) (hc : ContinuousOn G U) :
    AEMeasurable (density G) (μ.restrict U) := by
  classical
  let q : X → ℝ≥0∞ := U.piecewise (density G) (fun _ => 0)
  have hq : Measurable q := (continuousOn_density G U hc).measurable_piecewise continuousOn_const hU
  apply hq.aemeasurable.congr
  filter_upwards [ae_restrict_mem hU] with x hx
  exact Set.piecewise_eq_of_mem U _ _ hx

theorem density_pos {X : Type*} (G : X → Matrix Index Index ℝ) (x : X)
    (hx : Matrix.det (G x) ≠ 0) : 0 < density G x :=
  ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (abs_pos.mpr hx))

theorem density_ne_top {X : Type*} (G : X → Matrix Index Index ℝ) (x : X) :
    density G x ≠ ∞ := ENNReal.ofReal_ne_top

theorem withDensity_density_open_pos {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    (G : X → Matrix Index Index ℝ) (U : Set X) (hU : MeasurableSet U)
    (hc : ContinuousOn G U) (hdet : ∀ x ∈ U, Matrix.det (G x) ≠ 0)
    {V : Set X} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < μ.withDensity (density G) V :=
  Burnett.Analysis.PositiveDensity.withDensity_open_pos_of_forall hU
    (aemeasurable_density_restrict μ G U hU hc) (fun x hx => density_pos G x (hdet x hx))
    hV hne hVU

theorem coordinateMeasure_open_pos
    (G : CoordinateSpace → Matrix Index Index ℝ) (U : Set CoordinateSpace) (hU : IsOpen U)
    (hc : ContinuousOn G U) (hdet : ∀ x ∈ U, Matrix.det (G x) ≠ 0)
    {V : Set CoordinateSpace} (hV : IsOpen V) (hne : V.Nonempty) (hVU : V ⊆ U) :
    0 < coordinateMeasure G V :=
  withDensity_density_open_pos volume G U hU.measurableSet hc hdet hV hne hVU

theorem ae_coordinateMeasure_restrict_eq
    (G : CoordinateSpace → Matrix Index Index ℝ) (U S : Set CoordinateSpace)
    (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hc : ContinuousOn G U) (hdet : ∀ x ∈ U, Matrix.det (G x) ≠ 0) :
    ae ((coordinateMeasure G).restrict S) = ae (volume.restrict S) := by
  apply Burnett.Analysis.PositiveDensity.ae_restrict_withDensity_eq hS hSU
    (aemeasurable_density_restrict volume G U hU.measurableSet hc)
  exact ae_restrict_of_forall_mem hU.measurableSet (fun x hx => density_pos G x (hdet x hx))

theorem eLpNorm_top_coordinateMeasure_eq_volume {F : Type*} [ENorm F]
    (G : CoordinateSpace → Matrix Index Index ℝ) (U S : Set CoordinateSpace)
    (hU : IsOpen U) (hS : MeasurableSet S) (hSU : S ⊆ U)
    (hc : ContinuousOn G U) (hdet : ∀ x ∈ U, Matrix.det (G x) ≠ 0) (f : CoordinateSpace → F) :
    eLpNorm f ∞ ((coordinateMeasure G).restrict S) = eLpNorm f ∞ (volume.restrict S) := by
  apply Burnett.Analysis.PositiveDensity.eLpNorm_top_restrict_withDensity_eq hS hSU
    (aemeasurable_density_restrict volume G U hU.measurableSet hc)
  exact ae_restrict_of_forall_mem hU.measurableSet (fun x hx => density_pos G x (hdet x hx))

/-- The absolute determinant is essential here, since det G may be negative. -/
theorem sqrt_abs_det_pullback (G A : Matrix Index Index ℝ) :
    Real.sqrt |Matrix.det (A.transpose * G * A)| = |A.det| * Real.sqrt |G.det| := by
  rw [det_pullback, abs_mul, abs_of_nonneg (sq_nonneg _),
    Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

theorem density_pullback (G : CoordinateSpace → Matrix Index Index ℝ)
    (φ : CoordinateSpace → CoordinateSpace)
    (J : CoordinateSpace → CoordinateSpace →L[ℝ] CoordinateSpace) (x : CoordinateSpace) :
    density (fun y => (derivativeMatrix (J y)).transpose * G (φ y) * derivativeMatrix (J y)) x =
      ENNReal.ofReal |(J x).det| * density G (φ x) := by
  simp only [density, sqrt_abs_det_pullback, det_derivativeMatrix,
    ENNReal.ofReal_mul (abs_nonneg _)]

/-- Genuine Jacobian change of variables for the actual computed pullback. -/
theorem map_pullback_coordinateMeasure_restrict
    (G : CoordinateSpace → Matrix Index Index ℝ)
    (φ : CoordinateSpace → CoordinateSpace)
    (J : CoordinateSpace → CoordinateSpace →L[ℝ] CoordinateSpace)
    (s : Set CoordinateSpace) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivWithinAt φ (J x) s x) (hi : InjOn φ s) :
    Measure.map φ ((coordinateMeasure
      (fun y => (derivativeMatrix (J y)).transpose * G (φ y) * derivativeMatrix (J y))).restrict s) =
      (coordinateMeasure G).restrict (φ '' s) := by
  have him : MeasurableSet (φ '' s) := measurable_image_of_fderivWithin hs hφ hi
  have hmeas : AEMeasurable φ (volume.restrict s) :=
    (show ContinuousOn φ s from fun x hx => (hφ x hx).continuousWithinAt).aemeasurable hs
  let w := fun y => density
    (fun z => (derivativeMatrix (J z)).transpose * G (φ z) * derivativeMatrix (J z)) y
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
    exact density_pullback G φ J x
  · simp only [mem_preimage, hxt, not_false_eq_true, indicator_of_notMem, mul_zero]

theorem map_coordinateMeasure_restrict_of_pullback
    (G H : CoordinateSpace → Matrix Index Index ℝ)
    (φ : CoordinateSpace → CoordinateSpace)
    (J : CoordinateSpace → CoordinateSpace →L[ℝ] CoordinateSpace)
    (s : Set CoordinateSpace) (hs : MeasurableSet s)
    (hφ : ∀ x ∈ s, HasFDerivWithinAt φ (J x) s x) (hi : InjOn φ s)
    (hG : ∀ x ∈ s, H x = (derivativeMatrix (J x)).transpose * G (φ x) * derivativeMatrix (J x)) :
    Measure.map φ ((coordinateMeasure H).restrict s) =
      (coordinateMeasure G).restrict (φ '' s) := by
  have hH : (coordinateMeasure H).restrict s =
      (coordinateMeasure (fun x => (derivativeMatrix (J x)).transpose * G (φ x) *
        derivativeMatrix (J x))).restrict s := by
    simp only [coordinateMeasure, restrict_withDensity hs]
    apply withDensity_congr_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    simp only [density, hG x hx]
  rw [hH]
  exact map_pullback_coordinateMeasure_restrict G φ J s hs hφ hi

theorem map_openPartialHomeomorph_pullback_coordinateMeasure
    (G : CoordinateSpace → Matrix Index Index ℝ)
    (e : OpenPartialHomeomorph CoordinateSpace CoordinateSpace)
    (hc : ContDiffOn ℝ 1 e e.source) :
    Measure.map e ((coordinateMeasure (fun x =>
      (derivativeMatrix (fderiv ℝ e x)).transpose * G (e x) *
        derivativeMatrix (fderiv ℝ e x))).restrict e.source) =
      (coordinateMeasure G).restrict e.target := by
  have hd : DifferentiableOn ℝ e e.source := hc.differentiableOn le_rfl
  rw [← e.image_source_eq_target]
  apply map_pullback_coordinateMeasure_restrict G e (fderiv ℝ e) e.source e.open_source.measurableSet
  · intro x hx
    exact ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  · exact e.injOn

section Manifold
open scoped Manifold
variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold (𝓘(ℝ, CoordinateSpace)) 1 M]

theorem map_chartTransition_pullback_coordinateMeasure
    (G : CoordinateSpace → Matrix Index Index ℝ) (c d : M) :
    Measure.map (chartTransition c d) ((coordinateMeasure (fun x =>
      (derivativeMatrix (fderiv ℝ (chartTransition c d) x)).transpose *
        G (chartTransition c d x) *
        derivativeMatrix (fderiv ℝ (chartTransition c d) x))).restrict
          (chartTransition c d).source) =
      (coordinateMeasure G).restrict (chartTransition c d).target :=
  map_openPartialHomeomorph_pullback_coordinateMeasure G (chartTransition c d)
    (contDiffOn_chartTransition c d)

end Manifold
end Burnett.Geometry.LorentzVolume
