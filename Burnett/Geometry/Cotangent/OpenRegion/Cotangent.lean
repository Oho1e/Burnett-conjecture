import Burnett.Geometry.Cotangent.OpenRegion.Metrics
import Burnett.Geometry.Cotangent.SmoothExtension

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Bundle
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitNullAngular (Phase)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Forget only the base-region membership of a cotangent vector. -/
def cotangentOpenVal (U : Opens M) (p : CotangentBundle U) : CotangentBundle M := ⟨p.1.val, p.2⟩

theorem cotangentChart_openVal (U : Opens M) (c : U) {p : CotangentBundle U}
    (hp : p ∈ cotangentSource c) : cotangentChart c.val (cotangentOpenVal U p) = cotangentChart c p := by
  apply Prod.ext
  · rfl
  · funext i
    simp only [cotangentChart, cotangentCoords, cotangentTrivialization_apply]
    change p.2 (tangentFrame c.val p.1.val (coordinateBasis i)) = p.2 (tangentFrame c p.1 (coordinateBasis i))
    rw [tangentFrame_openSubtype U c p.1 hp]
    rfl

omit [IsManifold Model ∞ M] in
theorem phaseTarget_openSubtype_subset (U : Opens M) (c : U) : phaseTarget c ⊆ phaseTarget c.val :=
  fun _ h => ⟨h.1.1, trivial⟩

/-- In the common chart, both inverse cotangent charts assemble identically. -/
theorem cotangentChartInverse_openVal (U : Opens M) (c : U) {q : Phase}
    (hq : q ∈ phaseTarget c) :
    cotangentOpenVal U (cotangentChartInverse c q) = cotangentChartInverse c.val q := by
  let p := cotangentChartInverse c q
  have hp : p ∈ cotangentSource c := cotangentChartInverse_mapsTo c hq
  have hpM : cotangentOpenVal U p ∈ cotangentSource c.val := hp.2
  calc
    cotangentOpenVal U p = cotangentChartInverse c.val (cotangentChart c.val (cotangentOpenVal U p)) :=
      (cotangentChart_left_inv c.val hpM).symm
    _ = cotangentChartInverse c.val q := by rw [cotangentChart_openVal U c hp, cotangentChart_right_inv c hq]

theorem contMDiff_cotangentOpenVal (U : Opens M) :
    ContMDiff CotangentModelWithCorners CotangentModelWithCorners ∞ (cotangentOpenVal U) := by
  intro p
  let c := p.1
  have hp : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  have hMap : MapsTo (cotangentChart c) (cotangentSource c) (phaseTarget c.val) :=
    (cotangentChart_mapsTo c).mono_right (phaseTarget_openSubtype_subset U c)
  have hcomp := (contMDiffOn_cotangentChartInverse c.val).comp (contMDiffOn_cotangentChart c) hMap
  have hlocal : ContMDiffOn CotangentModelWithCorners CotangentModelWithCorners ∞
      (cotangentOpenVal U) (cotangentSource c) := by
    apply hcomp.congr
    intro q hq
    rw [Function.comp_apply, ← cotangentChartInverse_openVal U c (cotangentChart_mapsTo c hq),
      cotangentChart_left_inv c hq]
  exact hlocal.contMDiffAt ((isOpen_cotangentSource c).mem_nhds hp)

end Burnett.Geometry.OpenRegion
