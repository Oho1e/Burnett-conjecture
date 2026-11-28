import Burnett.Analysis.TransportClosure.C04FixedCotangentSymplectic
import Burnett.Geometry.Cotangent.SmoothExtension

/-! Compatibility with the actual preferred cotangent atlas. -/

set_option autoImplicit false

namespace Burnett.Geometry.FixedCotangentChart

open Bundle Filter Set
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.MaximalChart Burnett.Geometry.CotangentAngularExtension
open scoped Manifold ContDiff Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The fixed lift agrees on the true overlap with the change of coordinates built
from the preferred charts and their actual cotangent inverses. -/
theorem fixedPhaseTransition_atPoint_eqOn (c d : M) :
    EqOn (fixedPhaseTransition (.atPoint c) (.atPoint d))
      (cotangentChart d ∘ cotangentChartInverse c) (phaseOverlap (.atPoint c) (.atPoint d)) := by
  intro z hz
  let p := cotangentChartInverse c z
  have hc : p.proj ∈ (chartAt CoordinateSpace c).source :=
    cotangentChartInverse_mapsTo c ⟨hz.1, trivial⟩
  have hd : p.proj ∈ (chartAt CoordinateSpace d).source := hz.2
  have hp : fixedChartPhase (.atPoint c) p = z :=
    (fixedChartPhase_preferred c p hc).trans (cotangentChart_right_inv c ⟨hz.1, trivial⟩)
  change fixedPhaseTransition (.atPoint c) (.atPoint d) z = cotangentChart d p
  rw [← hp, fixedPhaseTransition_fixedChartPhase (.atPoint c) (.atPoint d) p hc hd,
    fixedChartPhase_preferred d p hd]
  rfl

theorem cotangentChart_transition_symplectic (c d : M) (z : Phase)
    (hz : z ∈ phaseOverlap (.atPoint c) (.atPoint d)) (U V : Phase) :
    let D := fderiv ℝ (cotangentChart d ∘ cotangentChartInverse c) z
    phaseSymplectic (D U) (D V) = phaseSymplectic U V := by
  have hEq : fixedPhaseTransition (.atPoint c) (.atPoint d) =ᶠ[𝓝 z]
      cotangentChart d ∘ cotangentChartInverse c := by
    filter_upwards [(isOpen_phaseOverlap (.atPoint c) (.atPoint d)).mem_nhds hz] with y hy
    exact fixedPhaseTransition_atPoint_eqOn c d hy
  simpa only [← hEq.fderiv_eq] using
    fixedPhaseTransition_symplectic (.atPoint c) (.atPoint d) z hz U V

end Burnett.Geometry.FixedCotangentChart
