import Burnett.Geometry.ManifoldMetricTransition
import Burnett.Geometry.LorentzVolume

/-! The absolute-determinant coordinate densities of one actual fiberwise
bilinear field agree under a genuine chart transition. This is overlap
compatibility, not the construction of a global manifold measure. -/

noncomputable section

namespace Burnett.Geometry.ManifoldLorentzVolume

open MeasureTheory Set
open scoped Manifold ContDiff
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ChartVolume

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The component transformation is derived from the same actual bilinear
field B, not assumed as a matrix or density identity. In particular this
applies to Lorentzian fields; no positive-definite restriction is imposed. -/
theorem coordinateBilinear_geometric_measure_change
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c d : M) :
    Measure.map (chartTransition c d)
      ((LorentzVolume.coordinateMeasure (metricComponents (coordinateBilinear B c))).restrict
        (chartTransition c d).source) =
      (LorentzVolume.coordinateMeasure (metricComponents (coordinateBilinear B d))).restrict
        (chartTransition c d).target := by
  let e := chartTransition c d
  have hd : DifferentiableOn ℝ e e.source := (contDiffOn_chartTransition c d).differentiableOn le_rfl
  rw [← e.image_source_eq_target]
  refine LorentzVolume.map_coordinateMeasure_restrict_of_pullback
    (metricComponents (coordinateBilinear B d)) (metricComponents (coordinateBilinear B c))
    e (fderiv ℝ e) e.source e.open_source.measurableSet ?_ e.injOn ?_
  · intro x hx
    exact ((hd x hx).differentiableAt (e.open_source.mem_nhds hx)).hasFDerivAt.hasFDerivWithinAt
  · intro x hx
    exact coordinateBilinear_matrix_change B c d hx

end Burnett.Geometry.ManifoldLorentzVolume
