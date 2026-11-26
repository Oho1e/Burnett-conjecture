import Burnett.Geometry.ChartDifferential
import Burnett.Geometry.ManifoldLorentzSignature

set_option autoImplicit false
set_option maxHeartbeats 2800000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The canonical open-submanifold inclusion has the identity differential
in the actual tangent model. -/
theorem hasMFDerivAt_openSubtype_val (U : Opens M) (x : U) :
    HasMFDerivAt Model Model (Subtype.val : U → M) x (ContinuousLinearMap.id ℝ CoordinateSpace) := by
  have hnear : writtenInExtChartAt Model Model x (Subtype.val : U → M) =ᶠ[𝓝 (chartAt CoordinateSpace x x)]
      (id : CoordinateSpace → CoordinateSpace) := by
    let e := chartAt CoordinateSpace x
    have hx : e x ∈ e.target := e.mapsTo (mem_chart_source CoordinateSpace x)
    filter_upwards [e.open_target.mem_nhds hx] with y hy
    change (chartAt CoordinateSpace x.val) ((e.symm y).val) = y
    change e (e.symm y) = y
    exact e.right_inv hy
  refine ⟨continuous_subtype_val.continuousAt, ?_⟩
  exact ((hasFDerivAt_id (chartAt CoordinateSpace x x)).congr_of_eventuallyEq hnear).hasFDerivWithinAt

theorem mfderiv_openSubtype_val (U : Opens M) (x : U) :
    mfderiv Model Model (Subtype.val : U → M) x = ContinuousLinearMap.id ℝ CoordinateSpace :=
  (hasMFDerivAt_openSubtype_val U x).mfderiv

variable [IsManifold Model ∞ M]

/-- Inverse chart differentials of the open region and the ambient manifold
agree throughout the common preferred chart. -/
theorem tangentFrame_openSubtype (U : Opens M) (c x : U)
    (hx : x ∈ (chartAt CoordinateSpace c).source) :
    tangentFrame c x = tangentFrame c.val x.val := by
  let e := chartAt CoordinateSpace c
  let E := chartAt CoordinateSpace c.val
  let y := e x
  have hy : y ∈ e.target := e.mapsTo hx
  have hxM : x.val ∈ E.source := hx.2
  have hyM : E x.val = y := rfl
  have hNear : E.symm =ᶠ[𝓝 y] (Subtype.val : U → M) ∘ e.symm := by
    apply Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hy)
    exact E.subtypeRestr_symm_eqOn ⟨c⟩
  have hSmooth : ContMDiffOn Model Model ∞ e.symm e.target := contMDiffOn_chart_symm
  have hdiff : MDifferentiableAt Model Model e.symm y :=
    (hSmooth.contMDiffAt (e.open_target.mem_nhds hy)).mdifferentiableAt (by simp)
  have hderiv : mfderiv Model Model (Subtype.val : U → M) (e.symm y) = ContinuousLinearMap.id ℝ CoordinateSpace :=
    mfderiv_openSubtype_val U (e.symm y)
  rw [ChartDifferential.tangentFrame_eq_mfderiv_symm c x hx,
    ChartDifferential.tangentFrame_eq_mfderiv_symm c.val x.val hxM, hyM,
    hNear.mfderiv_eq (I := Model) (I' := Model),
    mfderiv_comp y (hasMFDerivAt_openSubtype_val U (e.symm y)).mdifferentiableAt hdiff,
    hderiv]
  apply ContinuousLinearMap.ext
  intro z
  rfl

end Burnett.Geometry.OpenRegion
