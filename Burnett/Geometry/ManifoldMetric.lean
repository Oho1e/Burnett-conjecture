import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas
import Burnett.Geometry.ConnectionDifference
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# A smooth manifold metric in an actual tangent chart

The coordinate bilinear form pulls the given smooth Riemannian metric back
along the inverse of the tangent bundle's preferred trivialization. The base
point is the inverse of the same preferred chart. Positivity and coordinate
regularity are proved on that chart's target. Values outside this target are
only a total-function convention; no global frame is asserted.

No RiemannianBundle factory is installed, so all existing norms and bundle
structures stay those used by the coordinate calculations.
-/

noncomputable section
open Bundle Set
open scoped Manifold ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference

namespace Burnett.Geometry.ManifoldMetric

open Bundle Set LinearMap

/-- The existing four-dimensional Euclidean coordinate model. -/
abbrev Model := 𝓘(ℝ, CoordinateSpace)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- A genuine smooth metric on the actual tangent bundle. -/
abbrev Metric := Bundle.ContMDiffRiemannianMetric Model ∞ CoordinateSpace (TangentSpace Model : M → Type _)

/-- The inverse tangent trivialization belonging to the chart at `c`. -/
def tangentFrame (c : M) (m : M) : CoordinateSpace →L[ℝ] TangentSpace Model m :=
  (trivializationAt CoordinateSpace (TangentSpace Model) c).symmL ℝ m

/-- The metric in the chart frame, still parameterized by a manifold point. -/
def frameMetric (r : Metric (M := M)) (c m : M) : LinearMap.BilinForm ℝ CoordinateSpace :=
  LinearMap.mk₂ ℝ (fun u v => r.inner m (tangentFrame c m u) (tangentFrame c m v))
    (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])

/-- The actual coordinate bilinear form on the target of the chart at `c`. -/
def coordinateMetric (r : Metric (M := M)) (c : M) (y : CoordinateSpace) :
    LinearMap.BilinForm ℝ CoordinateSpace := frameMetric r c ((chartAt CoordinateSpace c).symm y)

theorem contMDiffOn_frame (c : M) (v : CoordinateSpace) :
    ContMDiffOn Model (Model.prod Model) ∞
      (fun m => TotalSpace.mk' CoordinateSpace m (tangentFrame c m v))
      (chartAt CoordinateSpace c).source := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  change ContMDiffOn Model (Model.prod Model) ∞ _ e.baseSet
  apply e.contMDiffOn_section_baseSet_iff.mpr
  apply contMDiffOn_const.congr
  intro m hm
  change (e ⟨m, e.symmL ℝ m v⟩).2 = v
  simp only [Trivialization.symmL_apply]
  exact congrArg Prod.snd (e.apply_mk_symm hm v)


theorem contMDiffOn_frame_inner (r : Metric (M := M)) (c : M) (u v : CoordinateSpace) :
    ContMDiffOn Model 𝓘(ℝ, ℝ) ∞
      (fun m => frameMetric r c m u v) (chartAt CoordinateSpace c).source := by
  have hv := contMDiffOn_frame (M := M) c u
  have hw := contMDiffOn_frame (M := M) c v
  have h := r.contMDiff.contMDiffOn.clm_bundle_apply₂ hv hw
  intro m hm
  have hh := h m hm
  simp only [contMDiffWithinAt_totalSpace] at hh
  exact hh.2

theorem contDiffOn_coordinateMetric_apply (r : Metric (M := M)) (c : M)
    (u v : CoordinateSpace) :
    ContDiffOn ℝ ∞ (fun y => coordinateMetric r c y u v)
      (chartAt CoordinateSpace c).target := by
  exact ((contMDiffOn_frame_inner r c u v).comp
    contMDiffOn_chart_symm (chartAt CoordinateSpace c).symm_mapsTo).contDiffOn

theorem frameMetric_symm (r : Metric (M := M)) (c m : M) :
    (frameMetric r c m).IsSymm := by
  exact ⟨fun u v => r.symm m _ _⟩

theorem tangentFrame_injective (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    Function.Injective (tangentFrame c m) := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  exact (e.continuousLinearEquivAt ℝ m hm).symm.injective

theorem coordinateMetric_pos (r : Metric (M := M)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) (u : CoordinateSpace) (hu : u ≠ 0) :
    0 < coordinateMetric r c y u u := by
  apply r.pos
  exact fun hz => hu ((tangentFrame_injective c _
    ((chartAt CoordinateSpace c).symm_mapsTo hy)) (by simpa using hz))

theorem coordinateMetric_posDef (r : Metric (M := M)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    Matrix.PosDef (metricComponents (coordinateMetric r c) y) := by
  constructor
  · apply Matrix.IsHermitian.ext
    intro i j
    simpa only [star_trivial] using r.symm ((chartAt CoordinateSpace c).symm y)
      (tangentFrame c _ (coordinateBasis j)) (tangentFrame c _ (coordinateBasis i))
  · intro x hx
    have heq : (metricComponents (coordinateMetric r c) y : Matrix Index Index ℝ) =
        BilinForm.toMatrix coordinateBasis (coordinateMetric r c y) := by
      ext i j
      simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
    rw [heq]
    simp only [star_trivial]
    rw [BilinForm.dotProduct_toMatrix_mulVec]
    apply coordinateMetric_pos r c hy
    exact fun hz => hx (coordinateBasis.equivFun.symm.injective (by simpa using hz))

theorem contDiffOn_metricComponents (r : Metric (M := M)) (c : M) (i j : Index) :
    ContDiffOn ℝ ∞ (fun y => metricComponents (coordinateMetric r c) y i j)
      (chartAt CoordinateSpace c).target :=
  contDiffOn_coordinateMetric_apply r c (coordinateBasis i) (coordinateBasis j)

theorem coordinateMetric_symm (r : Metric (M := M)) (c : M) (y : CoordinateSpace) :
    (coordinateMetric r c y).IsSymm := frameMetric_symm r c _

theorem coordinateMetric_nondegenerate (r : Metric (M := M)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) : (coordinateMetric r c y).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ coordinateBasis
  have heq : BilinForm.toMatrix coordinateBasis (coordinateMetric r c y) =
      metricComponents (coordinateMetric r c) y := by
    ext i j
    simp only [BilinForm.toMatrix_apply, metricComponents, FiberMetric.covariant]
  rw [heq]
  exact ne_of_gt (coordinateMetric_posDef r c hy).det_pos

theorem tangentFrame_eq_mfderivWithin (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tangentFrame c m = mfderivWithin Model Model (extChartAt Model c).symm
      (Set.range Model) (extChartAt Model c m) :=
  TangentBundle.symmL_trivializationAt hm

/-- The coordinate representation at the coordinate image of a manifold point. -/
theorem coordinateMetric_at_chart (r : Metric (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    coordinateMetric r c (chartAt CoordinateSpace c m) = frameMetric r c m := by
  simp only [coordinateMetric, (chartAt CoordinateSpace c).left_inv hm]

/-- The precise C1 interface consumed by the existing coordinate connections. -/
theorem contDiffOn_metricComponents_one (r : Metric (M := M)) (c : M) (i j : Index) :
    ContDiffOn ℝ 1 (fun y => metricComponents (coordinateMetric r c) y i j)
      (chartAt CoordinateSpace c).target :=
  (contDiffOn_metricComponents r c i j).of_le (by norm_num)

end Burnett.Geometry.ManifoldMetric
