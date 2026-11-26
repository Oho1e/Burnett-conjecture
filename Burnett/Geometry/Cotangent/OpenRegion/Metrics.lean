import Burnett.Geometry.Cotangent.OpenRegion.Inclusion

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter Bundle
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The restriction keeps the original bilinear form on each genuine tangent fiber. -/
def restrictBilinear (U : Opens M) (g : Field (M := M)) : Field (M := U) := fun x => g x.val

theorem hasLorentzSignature_restrictBilinear (U : Opens M) {g : Field (M := M)}
    (hL : HasLorentzSignature g) : HasLorentzSignature (restrictBilinear U g) := fun x => hL x.val

variable [IsManifold Model ∞ M]

theorem isSmooth_restrictBilinear (U : Opens M) (g : Field (M := M)) (hg : IsSmooth g) :
    IsSmooth (restrictBilinear U g) := by
  intro c
  let F := CoordinateSpace →L[ℝ] CoordinateSpace →L[ℝ] ℝ
  let e := trivializationAt F (fun x : U => TangentSpace Model x →L[ℝ] TangentSpace Model x →L[ℝ] ℝ) c
  let E := trivializationAt F (fun x : M => TangentSpace Model x →L[ℝ] TangentSpace Model x →L[ℝ] ℝ) c.val
  have hc : c ∈ (chartAt CoordinateSpace c).source := mem_chart_source CoordinateSpace c
  have hcM : c.val ∈ (chartAt CoordinateSpace c.val).source := hc.2
  have hce : c ∈ e.baseSet := ⟨hc, hc, trivial⟩
  have hcE : c.val ∈ E.baseSet := ⟨hcM, hcM, trivial⟩
  have hCoord : ContMDiffAt Model 𝓘(ℝ, F) ∞ (fun x : M => (E ⟨x, g x⟩).2) c.val :=
    (E.contMDiffAt_section_iff (IB := Model) hcE).mp (hg c.val)
  apply (e.contMDiffAt_section_iff (IB := Model) hce).mpr
  have hComp : ContMDiffAt Model 𝓘(ℝ, F) ∞ (fun x : U => (E ⟨x.val, g x.val⟩).2) c :=
    hCoord.comp c contMDiff_subtype_val.contMDiffAt
  apply (Filter.EventuallyEq.contMDiffAt_iff ?_).mpr hComp
  filter_upwards [(chartAt CoordinateSpace c).open_source.mem_nhds hc] with x hx
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousLinearMap.ext
  intro w
  letI : MemTrivializationAtlas (Bundle.Trivial.trivialization U ℝ) := ⟨Set.mem_singleton _⟩
  letI : MemTrivializationAtlas (Bundle.Trivial.trivialization M ℝ) := ⟨Set.mem_singleton _⟩
  let h := (trivializationAt CoordinateSpace (TangentSpace Model : U → Type _) c).continuousLinearMap
    (RingHom.id ℝ) (Bundle.Trivial.trivialization U ℝ)
  let H := (trivializationAt CoordinateSpace (TangentSpace Model : M → Type _) c.val).continuousLinearMap
    (RingHom.id ℝ) (Bundle.Trivial.trivialization M ℝ)
  change (h.continuousLinearMapAt ℝ x (g x.val (tangentFrame c x v))) w =
    (H.continuousLinearMapAt ℝ x.val (g x.val (tangentFrame c.val x.val v))) w
  rw [Trivialization.continuousLinearMapAt_apply, Trivialization.continuousLinearMapAt_apply,
    h.coe_linearMapAt_of_mem (show x ∈ h.baseSet from ⟨hx, trivial⟩),
    H.coe_linearMapAt_of_mem (show x.val ∈ H.baseSet from ⟨hx.2, trivial⟩)]
  simp only [h, H, Trivialization.continuousLinearMap_apply, ContinuousLinearMap.comp_apply,
    Bundle.Trivial.continuousLinearMapAt_trivialization, ContinuousLinearMap.id_apply]
  change g x.val (tangentFrame c x v) (tangentFrame c x w) =
    g x.val (tangentFrame c.val x.val v) (tangentFrame c.val x.val w)
  rw [tangentFrame_openSubtype U c x hx]
  rfl

/-- The auxiliary metric is restricted along the same inclusion. -/
def restrictRiemannian (U : Opens M) (r : Metric (M := M)) : Metric (M := U) where
  inner := restrictBilinear U r.inner
  symm x := r.symm x.val
  pos x := r.pos x.val
  isVonNBounded x := r.isVonNBounded x.val
  contMDiff := isSmooth_restrictBilinear U r.inner r.contMDiff

/-- The original and restricted metric coefficients agree on the open
submanifold chart target, in the same preferred coordinates. -/
theorem coordinateBilinear_openSubtype (U : Opens M) (g : Field (M := M)) (c : U)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateBilinear (restrictBilinear U g) c y = coordinateBilinear g c.val y := by
  let e := chartAt CoordinateSpace c
  let E := chartAt CoordinateSpace c.val
  let x := e.symm y
  have hx : x ∈ e.source := e.symm_mapsTo hy
  have hEq : E.symm y = x.val := E.subtypeRestr_symm_eqOn ⟨c⟩ hy
  apply LinearMap.ext
  intro a
  apply LinearMap.ext
  intro b
  change g x.val (tangentFrame c x a) (tangentFrame c x b) =
    g (E.symm y) (tangentFrame c.val (E.symm y) a) (tangentFrame c.val (E.symm y) b)
  rw [tangentFrame_openSubtype U c x hx, hEq]
  rfl

end Burnett.Geometry.OpenRegion
