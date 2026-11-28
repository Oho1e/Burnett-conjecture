import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
import Burnett.Analysis.TransportWard.Weyl.LocalSchwartzCoefficients

/-! Actual chart density coefficients on one common compact plateau. -/

set_option autoImplicit false
set_option maxHeartbeats 4600000

noncomputable section

namespace Burnett.V03.Palatini

open Set Filter Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped ContDiff Topology Matrix.Norms.Elementwise

local notation "E₀" => CoordinateSpace
local notation "J" => Fin 4 × Fin 4

/-- One genuine compact window extends all density coefficients without
altering any coefficient germ in an open neighborhood of the window. -/
theorem exists_densityPrincipalCoefficients_schwartz_near {ι : Type*}
    (S : ι → Mat) (G : E₀ → Mat) {K U : Set E₀} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (hG : ContDiffOn ℝ ∞ G U) (hn : MapsTo G U nonsingularMetricDomain) :
    ∃ V : Set E₀, IsOpen V ∧ K ⊆ V ∧ V ⊆ U ∧
      ∃ c : ι → ι → J → SchwartzMap E₀ ℂ,
        ∀ i j d x, x ∈ V →
          DifferentiableAt ℝ (fun y => metricActionCoefficient S (d.1,i) (d.2,j) (G y)) x ∧
          (fun y : E₀ => c i j d y) =ᶠ[𝓝 x]
            (fun y => (metricActionCoefficient S (d.1,i) (d.2,j) (G y) : ℂ)) := by
  let r (s : ι × ι × J) (y : E₀) :=
    metricActionCoefficient S (s.2.2.1,s.1) (s.2.2.2,s.2.1) (G y)
  have hr (s : ι × ι × J) : ContDiffOn ℝ ∞ (r s) U := by
    change ContDiffOn ℝ ∞ (metricActionCoefficient S (s.2.2.1,s.1) (s.2.2.2,s.2.1) ∘ G) U
    exact (contDiffOn_metricActionCoefficient S _ _).comp hG hn
  obtain ⟨V,hV,hKV,hVU,c,hc⟩ := exists_schwartzCoefficients_complex_near r hK hU hKU hr
  exact ⟨V,hV,hKV,hVU,fun i j d => c (i,j,d),fun i j d x hx =>
    ⟨((hr (i,j,d)).contDiffAt (hU.mem_nhds (hVU hx))).differentiableAt (by simp),hc (i,j,d) x hx⟩⟩

end Burnett.V03.Palatini
