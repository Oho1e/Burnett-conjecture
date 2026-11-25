import Burnett.Geometry.Cotangent.CanonicalTrajectories
import Burnett.Geometry.Cotangent.WeightedMomentumTransport

set_option autoImplicit false
set_option maxHeartbeats 2800000
set_option maxRecDepth 3300

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter
open scoped ContDiff Topology Manifold
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.UnitNullAngular Burnett.Geometry.RadialHamilton
open Burnett.Geometry.CotangentCauchyCrossing Burnett.Geometry.CotangentHamiltonLocalFlow
open Burnett.Geometry.CotangentHamiltonMaximalCurve
open Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The actual Hamilton derivative used in the measure equation equals the
ordinary time derivative of the test along the genuine canonical orbit. -/
theorem hasDerivAt_testAlong_canonicalTrajectory (g : Field (M := M)) (hg : IsSmooth g)
    (hn : IsNondegenerate g) (hs : IsSymmetric g) {p : CotangentBundle M}
    (A : CanonicalTrajectory g p) {t : ℝ} (ht : t ∈ A.domain) (hp : A.curve t ∈ puncturedCotangent)
    (a : CotangentBundle M → ℝ) (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent) :
    HasDerivAt (a ∘ A.curve) (actualHamiltonDerivative g a (A.curve t)) t := by
  let c := (A.curve t).1
  have hc : A.curve t ∈ cotangentSource c := mem_chart_source CoordinateSpace _
  obtain ⟨J, hJ, htJ, _, hChart⟩ :=
    canonicalCurve_chart_near g hg hn hs c A.curve A.domain A.domain_open A.integral t ht hc
  let x (b : ℝ) := cotangentChart c (A.curve b)
  let aC := a ∘ cotangentChartInverse c
  have hx : x t ∈ puncturedPhaseTarget c := cotangentChart_mem_punctured c _ hc hp
  have hDer := ((contDiffOn_cotangent_test_chart c a ha).contDiffAt
    ((isOpen_puncturedPhaseTarget c).mem_nhds hx)).differentiableAt (by simp)
  have hTime : HasDerivAt (aC ∘ x) (chartHamiltonDerivative g c a (A.curve t)) t :=
    hDer.hasFDerivAt.comp_hasDerivAt t (hChart.2 t htJ)
  rw [actualHamiltonDerivative_in_chart g hg hn hs a ha c hc hp]
  apply hTime.congr_of_eventuallyEq
  filter_upwards [hJ.mem_nhds htJ] with b hb
  change a (A.curve b) = a (cotangentChartInverse c (cotangentChart c (A.curve b)))
  rw [cotangentChart_left_inv c (hChart.1 b hb)]

end Burnett.Geometry.CotangentHamiltonInitialFamily
