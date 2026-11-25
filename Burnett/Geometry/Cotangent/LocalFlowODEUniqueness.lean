import Mathlib.Analysis.ODE.Gronwall

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace Burnett.Geometry.CotangentHamiltonInitialFamily

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Agreement at one time of two actual autonomous solutions propagates over
their common connected open interval of definition. -/
theorem eqOn_autonomousSolutions_of_locallyLipschitz {f : E → E}
    {J : Set ℝ} {t₀ : ℝ} (hJ : IsOpen J) (hConnected : IsPreconnected J)
    (t₀J : t₀ ∈ J) (hf : LocallyLipschitz f) {u v : ℝ → E}
    (hu : ∀ t ∈ J, HasDerivAt u (f (u t)) t)
    (hv : ∀ t ∈ J, HasDerivAt v (f (v t)) t)
    (h₀ : u t₀ = v t₀) : EqOn u v J := by
  let S : Set J := {t | u t = v t}
  letI : PreconnectedSpace J := isPreconnected_iff_preconnectedSpace.mp hConnected
  have huCont : ContinuousOn u J := fun t ht => (hu t ht).continuousAt.continuousWithinAt
  have hvCont : ContinuousOn v J := fun t ht => (hv t ht).continuousAt.continuousWithinAt
  have hClosed : IsClosed S := isClosed_eq huCont.restrict hvCont.restrict
  have hOpen : IsOpen S := by
    refine isOpen_iff_mem_nhds.mpr fun t ht => ?_
    have heq : u t = v t := ht
    obtain ⟨K, W, hW, hLip⟩ := hf (u t)
    have hJt : ∀ᶠ s : ℝ in 𝓝 (t : ℝ), s ∈ J := hJ.mem_nhds t.property
    have huW : ∀ᶠ s in 𝓝 (t : ℝ), u s ∈ W :=
      (hu t t.property).continuousAt.preimage_mem_nhds hW
    have hvW : ∀ᶠ s in 𝓝 (t : ℝ), v s ∈ W :=
      (hv t t.property).continuousAt.preimage_mem_nhds (heq ▸ hW)
    have he : u =ᶠ[𝓝 (t : ℝ)] v :=
      ODE_solution_unique_of_eventually (v := fun _ => f) (K := K) (s := fun _ => W)
        (Eventually.of_forall fun _ => hLip)
        ((hJt.mono fun s hs => hu s hs).and huW)
        ((hJt.mono fun s hs => hv s hs).and hvW) heq
    exact continuous_subtype_val.continuousAt.eventually he
  have hAll : S = univ := (show IsClopen S from ⟨hClosed, hOpen⟩).eq_univ ⟨⟨t₀, t₀J⟩, h₀⟩
  intro t ht
  have hh : (⟨t, ht⟩ : J) ∈ S := hAll ▸ mem_univ _
  exact hh

end Burnett.Geometry.CotangentHamiltonInitialFamily
