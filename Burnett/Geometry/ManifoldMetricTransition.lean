import Burnett.Geometry.ManifoldMetric
import Burnett.Geometry.ChartVolume
import Burnett.Geometry.TensorCoordinateChange

/-!
# One bilinear field in two actual manifold charts

The preferred tangent frames transform by the actual Frechet derivative
of chart_d composed with chart_c.symm. This is derived from the tangent
bundle core cocycle, rather than supplied as a transition hypothesis.

The resulting bilinear and matrix laws apply to any genuine field of
continuous bilinear forms on the tangent fibers. No positivity, symmetry,
or regularity of that field is needed for these pointwise identities.
The given smooth Riemannian metric is then instantiated, and the already
proved coordinate Jacobian bridge yields equality of its two restricted
coordinate measures. No global manifold volume or physical dV_g is built.
-/

noncomputable section
open Bundle Set Matrix LinearMap
open Burnett.RicciSymbol
open scoped Manifold ContDiff
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ChartVolume

namespace Burnett.Geometry.ManifoldMetricTransition

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem tangentCoordChange_eq_fderiv_chartTransition (c d m : M) :
    tangentCoordChange Model c d m =
      fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m) := by
  simp only [tangentCoordChange_def, Model, mfld_simps, chartTransition, fderivWithin_univ]

/-- Equality in one tangent fiber; both preferred charts contain m. -/
theorem tangentFrame_change (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) (v : CoordinateSpace) :
    tangentFrame c m v = tangentFrame d m
      (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m) v) := by
  simp only [tangentFrame, TangentBundle.symmL_trivializationAt_eq_core hc,
    TangentBundle.symmL_trivializationAt_eq_core hd]
  change tangentCoordChange Model c m m v =
    tangentCoordChange Model d m m
      (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m) v)
  rw [← tangentCoordChange_eq_fderiv_chartTransition]
  symm
  apply tangentCoordChange_comp
  simpa only [Model, mfld_simps] using
    (show m ∈ (chartAt CoordinateSpace c).source ∩ (chartAt CoordinateSpace d).source ∩
      (chartAt CoordinateSpace m).source from ⟨⟨hc, hd⟩, mem_chart_source _ m⟩)


omit [IsManifold Model ∞ M] in
theorem chartTransition_symm_point (c d : M) {y : CoordinateSpace}
    (hy : y ∈ (chartTransition c d).source) :
    (chartAt CoordinateSpace d).symm (chartTransition c d y) =
      (chartAt CoordinateSpace c).symm y :=
  (chartAt CoordinateSpace d).left_inv hy.2

theorem tangentFrame_change_coordinates (c d : M) {y : CoordinateSpace}
    (hy : y ∈ (chartTransition c d).source) (v : CoordinateSpace) :
    tangentFrame c ((chartAt CoordinateSpace c).symm y) v =
      tangentFrame d ((chartAt CoordinateSpace c).symm y)
        (fderiv ℝ (chartTransition c d) y v) := by
  have h := tangentFrame_change c d ((chartAt CoordinateSpace c).symm y)
    ((chartAt CoordinateSpace c).symm_mapsTo hy.1) hy.2 v
  simpa only [(chartAt CoordinateSpace c).right_inv hy.1] using h

/-- Actual pullback of the same fiberwise bilinear form along one tangent frame. -/
def frameBilinear
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c m : M) : LinearMap.BilinForm ℝ CoordinateSpace :=
  LinearMap.mk₂ ℝ (fun u v => B m (tangentFrame c m u) (tangentFrame c m v))
    (by intros; simp [map_add]) (by intros; simp [map_smul])
    (by intros; simp [map_add]) (by intros; simp [map_smul])

def coordinateBilinear
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c : M) (y : CoordinateSpace) : LinearMap.BilinForm ℝ CoordinateSpace :=
  frameBilinear B c ((chartAt CoordinateSpace c).symm y)

theorem coordinateBilinear_inner (r : Metric (M := M)) (c : M) (y : CoordinateSpace) :
    coordinateBilinear r.inner c y = coordinateMetric r c y := rfl

theorem coordinateBilinear_change_apply
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c d : M) {y : CoordinateSpace} (hy : y ∈ (chartTransition c d).source)
    (u v : CoordinateSpace) :
    coordinateBilinear B c y u v = coordinateBilinear B d (chartTransition c d y)
      (fderiv ℝ (chartTransition c d) y u) (fderiv ℝ (chartTransition c d) y v) := by
  change B ((chartAt CoordinateSpace c).symm y)
      (tangentFrame c ((chartAt CoordinateSpace c).symm y) u)
      (tangentFrame c ((chartAt CoordinateSpace c).symm y) v) =
    B ((chartAt CoordinateSpace d).symm (chartTransition c d y))
      (tangentFrame d ((chartAt CoordinateSpace d).symm (chartTransition c d y))
        (fderiv ℝ (chartTransition c d) y u))
      (tangentFrame d ((chartAt CoordinateSpace d).symm (chartTransition c d y))
        (fderiv ℝ (chartTransition c d) y v))
  rw [chartTransition_symm_point c d hy,
    tangentFrame_change_coordinates c d hy u, tangentFrame_change_coordinates c d hy v]

theorem coordinateBilinear_change
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c d : M) {y : CoordinateSpace} (hy : y ∈ (chartTransition c d).source) :
    coordinateBilinear B c y =
      (coordinateBilinear B d (chartTransition c d y)).comp
        (fderiv ℝ (chartTransition c d) y).toLinearMap
        (fderiv ℝ (chartTransition c d) y).toLinearMap := by
  ext u v
  exact coordinateBilinear_change_apply B c d hy u v

theorem metricComponents_eq_toMatrix
    (b : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace) (y : CoordinateSpace) :
    metricComponents b y = BilinForm.toMatrix coordinateBasis (b y) := by
  ext i j
  simp only [BilinForm.toMatrix_apply, metricComponents, Burnett.Geometry.FiberMetric.covariant]

/-- The genuine covariant matrix law. pullbackMetric fixes matrix multiplication
explicitly, avoiding the function-array pointwise multiplication instance. -/
theorem coordinateBilinear_matrix_change
    (B : ∀ m : M, TangentSpace Model m →L[ℝ] TangentSpace Model m →L[ℝ] ℝ)
    (c d : M) {y : CoordinateSpace} (hy : y ∈ (chartTransition c d).source) :
    (metricComponents (coordinateBilinear B c) y : Matrix Index Index ℝ) =
      TensorCoordinateChange.pullbackMetric
        (metricComponents (coordinateBilinear B d) (chartTransition c d y))
        (derivativeMatrix (fderiv ℝ (chartTransition c d) y)) := by
  simp only [metricComponents_eq_toMatrix]
  rw [coordinateBilinear_change B c d hy]
  simpa only [TensorCoordinateChange.pullbackMetric, derivativeMatrix] using
    (BilinForm.toMatrix_comp (b := coordinateBasis) (c := coordinateBasis)
      (coordinateBilinear B d (chartTransition c d y))
      (fderiv ℝ (chartTransition c d) y).toLinearMap
      (fderiv ℝ (chartTransition c d) y).toLinearMap)

theorem coordinateMetric_matrix_change (r : Metric (M := M))
    (c d : M) {y : CoordinateSpace} (hy : y ∈ (chartTransition c d).source) :
    (metricComponents (coordinateMetric r c) y : Matrix Index Index ℝ) =
      TensorCoordinateChange.pullbackMetric
        (metricComponents (coordinateMetric r d) (chartTransition c d y))
        (derivativeMatrix (fderiv ℝ (chartTransition c d) y)) := by
  exact coordinateBilinear_matrix_change r.inner c d hy

/-- The same auxiliary Riemannian metric supplies both coordinate measures.
Only their genuine chart overlap is restricted; no density or measure relation
is an assumption. This is not an identification with the physical Lorentz volume. -/
theorem coordinateMetric_measure_change (r : Metric (M := M)) (c d : M) :
    MeasureTheory.Measure.map (chartTransition c d)
      ((Burnett.Geometry.RiemannianVolume.coordinateMeasure (metricComponents (coordinateMetric r c))).restrict
        (chartTransition c d).source) =
      (Burnett.Geometry.RiemannianVolume.coordinateMeasure (metricComponents (coordinateMetric r d))).restrict
        (chartTransition c d).target :=
  map_chartTransition_coordinateMeasure_of_pullback
    (metricComponents (coordinateMetric r d)) (metricComponents (coordinateMetric r c)) c d
    (fun _ hy => coordinateMetric_matrix_change r c d hy)

end Burnett.Geometry.ManifoldMetricTransition
