import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives
import Burnett.Analysis.CubicEnergy.FourierPairing

set_option autoImplicit false
noncomputable section
namespace Burnett.V11
open Set Filter
open Burnett.P01 Burnett.A02.FrequencySplit
open scoped ContDiff Topology

/-- A smooth local test has a global-in-center representative equal on every
frequency fiber over the original compact window, including frequency zero. -/
theorem exists_local_frequency_test_extension (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (a : Joint → ℝ) (ha : ContDiffOn ℝ ∞ a (U ×ˢ {ξ : E | ξ ≠ 0})) :
    ∃ b : Joint → ℝ, ContDiffOn ℝ ∞ b {p : Joint | p.2 ≠ 0} ∧ ∀ x ∈ K, ∀ ξ, b (x,ξ)=a (x,ξ) := by
  obtain ⟨χ,hχ,_,supp,V,_,sub,_,one⟩ := exists_projectedChartCutoff hK hU hKU
  refine ⟨fun p => χ p.1*a p,?_,?_⟩
  · intro p hp
    by_cases h : p.1 ∈ tsupport χ
    · have ho : IsOpen (U ×ˢ {ξ : E | ξ ≠ 0}) := hU.prod (isOpen_ne_fun continuous_id continuous_const)
      exact (((hχ.comp contDiff_fst).contDiffAt).mul (ha.contDiffAt (ho.mem_nhds ⟨supp h,hp⟩))).contDiffWithinAt
    · have zero := (notMem_tsupport_iff_eventuallyEq.mp h).comp_tendsto (continuous_fst.continuousAt (x:=p)).tendsto
      have eq : (fun q : Joint => χ q.1*a q) =ᶠ[𝓝 p] (fun _ => 0) := by
        filter_upwards [zero] with q hq
        change χ q.1=0 at hq
        simp [hq]
      exact ((contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq eq).contDiffWithinAt
  · intro x hx ξ
    change χ x*a (x,ξ)=a (x,ξ)
    rw [one (sub hx)]; simp

end Burnett.V11
