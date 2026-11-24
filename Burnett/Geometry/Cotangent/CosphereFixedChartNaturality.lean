import Burnett.Geometry.Cotangent.CosphereMeasure
import Burnett.Geometry.Cotangent.FixedChartNaturality

/-! Fixed-chart pushforwards of one measure on the actual auxiliary unit cosphere. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.UnitCosphere

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldMetric MaximalChart
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

abbrev fixedChartPhase {r : Metric (M := M)} (c : AtlasChart M) : Cosphere r → FixedCotangentChart.Phase :=
  FixedCotangentChart.fixedChartPhase c ∘ Subtype.val

/-- The scalar chart laws on the genuine base overlap for a single cosphere measure. -/
def FixedChartNaturality {r : Metric (M := M)} (μ : Measure (Cosphere r)) : Prop :=
  ∀ c d : AtlasChart M,
    let ν := μ.restrict (projection ⁻¹' (c.chart.source ∩ d.chart.source))
    let μc := Measure.map (fixedChartPhase c) ν
    let μd := Measure.map (fixedChartPhase d) ν
    AEMeasurable (fixedChartPhase c) ν ∧
      AEMeasurable (fixedChartPhase d) ν ∧
      AEMeasurable (FixedCotangentChart.fixedPhaseTransition c d) μc ∧
      Measure.map (FixedCotangentChart.fixedPhaseTransition c d) μc = μd

theorem fixedChartNaturality {r : Metric (M := M)} (μ : Measure (Cosphere r)) :
    FixedChartNaturality μ :=
  fun c d => FixedCotangentChart.fixedChart_pushforwards Subtype.val continuous_subtype_val μ c d

end Burnett.Geometry.UnitCosphere
