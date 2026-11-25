import Burnett.Geometry.Causality.ChronologicalVolume

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set Filter
open scoped Topology

variable {M : Type*} [TopologicalSpace M]

/-- An ordered path that repeatedly returns to a causally convex neighborhood
eventually stays in it, since every intervening point lies between two visits. -/
theorem tendsto_atTop_of_convex_neighborhoods_of_clusterPt {ι : Type*} [LinearOrder ι] [Nonempty ι]
    (R : M → M → Prop) (γ : ι → M) (hγ : ∀ {i j : ι}, i ≤ j → R (γ i) (γ j))
    {x : M} (hx : MapClusterPt x atTop γ)
    (hLocal : ∀ U ∈ 𝓝 x, ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → R a z → R z b → z ∈ V) :
    Tendsto γ atTop (𝓝 x) := by
  apply tendsto_def.mpr
  intro U hU
  obtain ⟨V, hV, hVU, hconv⟩ := hLocal U hU
  have hreturn := frequently_atTop.mp (mapClusterPt_iff_frequently.mp hx V hV)
  obtain ⟨i, _, hi⟩ := hreturn (Classical.arbitrary ι)
  apply eventually_atTop.mpr
  refine ⟨i, fun j hij => ?_⟩
  obtain ⟨k, hjk, hk⟩ := hreturn j
  exact hVU (hconv hi hk (hγ hij) (hγ hjk))

/-- Compact causal diamonds and causally convex neighborhoods prohibit an
ordered path with no future limit from having a common causal upper endpoint. -/
theorem iInter_future_eq_empty_of_no_limit {ι : Type*} [LinearOrder ι] [Nonempty ι]
    [NeBot (atTop : Filter ι)] (R : M → M → Prop) (γ : ι → M)
    (hγ : ∀ {i j : ι}, i ≤ j → R (γ i) (γ j))
    (hLoc : ∀ (x : M) (U : Set M), U ∈ 𝓝 x → ∃ V ∈ 𝓝 x, V ⊆ U ∧
      ∀ ⦃a z b : M⦄, a ∈ V → b ∈ V → R a z → R z b → z ∈ V)
    (hCompact : ∀ a b : M, IsCompact {z : M | R a z ∧ R z b})
    (hNoLim : ∀ x : M, ¬ Tendsto γ atTop (𝓝 x)) :
    (⋂ i, {x : M | R (γ i) x}) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro b hb
  let i : ι := Classical.arbitrary _
  have hTail : ∀ᶠ j in atTop, γ j ∈ {z : M | R (γ i) z ∧ R z b} :=
    eventually_atTop.mpr ⟨i, fun j hij => ⟨hγ hij, mem_iInter.mp hb j⟩⟩
  have hMem : {z : M | R (γ i) z ∧ R z b} ∈ Filter.map γ atTop := hTail
  obtain ⟨x, _, hx⟩ := (hCompact (γ i) b).exists_mapClusterPt (le_principal_iff.mpr hMem)
  exact hNoLim x (tendsto_atTop_of_convex_neighborhoods_of_clusterPt R γ (fun h => hγ h) hx (hLoc x))

end Burnett.Geometry.FiniteCausalVolume
