import Burnett.Geometry.Cotangent.OpenRegion.Cotangent

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Bundle
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.UnitNullCompactness Burnett.Geometry.CotangentAngularExtension

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Ambient cotangent vectors with base point in the chosen open region. -/
def cotangentOver (U : Opens M) : Set (CotangentBundle M) := (fun p => p.1) ⁻¹' (U : Set M)

theorem isOpen_cotangentOver (U : Opens M) : IsOpen (cotangentOver U) :=
  U.isOpen.preimage continuous_cotangent_projection

private def cotangentOpenLift (U : Opens M) (p : cotangentOver U) : CotangentBundle U :=
  ⟨⟨p.val.1, p.property⟩, p.val.2⟩

private theorem continuous_cotangentOpenLift (U : Opens M) : Continuous (cotangentOpenLift U) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  let c : U := ⟨p.val.1, p.property⟩
  let s : Set (cotangentOver U) := Subtype.val ⁻¹' cotangentSource c.val
  have hs : IsOpen s := (isOpen_cotangentSource c.val).preimage continuous_subtype_val
  have hp : p ∈ s := mem_chart_source CoordinateSpace p.val.1
  let L := (cotangentChart c.val) ∘ (Subtype.val : cotangentOver U → CotangentBundle M)
  have hL : ContinuousOn L s :=
    (contMDiffOn_cotangentChart c.val).continuousOn.comp continuous_subtype_val.continuousOn (fun _ h => h)
  have hEq (q : cotangentOver U) (hq : q ∈ s) : L q = cotangentChart c (cotangentOpenLift U q) := by
    have hqu : cotangentOpenLift U q ∈ cotangentSource c := ⟨trivial, hq⟩
    exact cotangentChart_openVal U c hqu
  have hmap : MapsTo L s (phaseTarget c) := by
    intro q hq
    rw [hEq q hq]
    exact cotangentChart_mapsTo c (show cotangentOpenLift U q ∈ cotangentSource c from ⟨trivial, hq⟩)
  have hcomp := (contMDiffOn_cotangentChartInverse c).continuousOn.comp hL hmap
  have hlocal : ContinuousOn (cotangentOpenLift U) s := by
    apply hcomp.congr
    intro q hq
    rw [Function.comp_apply, hEq q hq, cotangentChart_left_inv c (show cotangentOpenLift U q ∈ cotangentSource c from ⟨trivial, hq⟩)]
  exact hlocal.continuousAt (hs.mem_nhds hp)

/-- The cotangent bundle of an open submanifold is precisely the restriction
of the original bundle to that base region. -/
def cotangentOpenHomeomorph (U : Opens M) : CotangentBundle U ≃ₜ cotangentOver U where
  toFun p := ⟨cotangentOpenVal U p, p.1.property⟩
  invFun := cotangentOpenLift U
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (contMDiff_cotangentOpenVal U).continuous.subtype_mk _
  continuous_invFun := continuous_cotangentOpenLift U

theorem cotangentOpenVal_isOpenEmbedding (U : Opens M) : Topology.IsOpenEmbedding (cotangentOpenVal U) :=
  (isOpen_cotangentOver U).isOpenEmbedding_subtypeVal.comp (cotangentOpenHomeomorph U).isOpenEmbedding

end Burnett.Geometry.OpenRegion
