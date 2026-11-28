import Burnett.Analysis.TransportWard.Weyl.PointwiseVacuum

/-! The affine Euler path of the original chart fields. -/

set_option autoImplicit false
set_option maxRecDepth 4500
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.V03.Palatini

open Set Filter MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear
open scoped ContDiff InnerProductSpace Manifold Topology Matrix.Norms.Elementwise

local notation "E" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- The variation in the actual independent lower coordinate slots. -/
def originalChartPerturbation (B₀ B₁ : Field (M := M)) (c : M) (y : E) : I → ℝ :=
  symmetricChartMetricComponents B₁ c y - symmetricChartMetricComponents B₀ c y

/-- The exact Euler density along the affine path of the two original metrics. -/
def originalChartEulerPath (B₀ B₁ : Field (M := M)) (c : M) (t : ℝ) (x : E) (i : I) : ℝ :=
  coordinateDensityEuler symmetricMetricDirection
    (fun y => symmetricChartMetricComponents B₀ c y + t • originalChartPerturbation B₀ B₁ c y)
    x i

end Burnett.V03.Palatini
