import Burnett.Geometry.ManifoldBilinear

/-!
# The physical covariant-two norm on actual tangent fibers

At m the definition uses the preferred tangent frame indexed by m. The
actual frame cocycle and matrix determinant prove that every chart-change
matrix is a unit. The same-field pullback law and true covariant-two norm
invariance then identify this value with the contraction in any fixed
chart containing m. No globally smooth frame is chosen.

The norm is the actual inverse-r/inverse-r ordered contraction and is
proved equal to its genuine ofMatrix Hilbert norm. It is never the curried
Hom operator norm. No regularity or positivity of B is assumed.
-/

noncomputable section
open Bundle Set LinearMap
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldMetricTransition

namespace Burnett.Geometry.ManifoldTensorNorm

open Filter Matrix
open scoped Topology BigOperators
open Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ChartVolume
open Burnett.Geometry.CovariantTensorNorm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

def frameComponents (B : Field (M := M)) (c m : M) : Matrix Index Index ℝ :=
  Burnett.Geometry.FiberMetric.covariant (frameBilinear B c m) coordinateBasis

theorem frameComponents_eq_coordinate (B : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    frameComponents B c m =
      (metricComponents (coordinateBilinear B c) (chartAt CoordinateSpace c m) : Matrix Index Index ℝ) := by
  simp only [frameComponents, metricComponents, coordinateBilinear, (chartAt CoordinateSpace c).left_inv hm]

theorem frameComponents_change (B : Field (M := M)) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source) :
    frameComponents B c m = TensorCoordinateChange.pullbackMetric (frameComponents B d m)
      (derivativeMatrix (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m))) := by
  have hy : chartAt CoordinateSpace c m ∈ (chartTransition c d).source := by
    constructor
    · exact (chartAt CoordinateSpace c).map_source hc
    · change (chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c m) ∈
        (chartAt CoordinateSpace d).source
      simpa only [(chartAt CoordinateSpace c).left_inv hc] using hd
  have hp : chartTransition c d (chartAt CoordinateSpace c m) = chartAt CoordinateSpace d m := by
    change chartAt CoordinateSpace d ((chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c m)) = _
    rw [(chartAt CoordinateSpace c).left_inv hc]
  have h := coordinateBilinear_matrix_change B c d hy
  rw [hp, ← frameComponents_eq_coordinate B c m hc, ← frameComponents_eq_coordinate B d m hd] at h
  exact h

theorem transitionMatrix_isUnit (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source) :
    IsUnit (derivativeMatrix (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m))) := by
  let J := fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)
  have hi : Function.Injective J := by
    intro u v huv
    apply ManifoldMetric.tangentFrame_injective c m hc
    exact (tangentFrame_change c d m hc hd u).trans
      ((congrArg (tangentFrame d m) huv).trans (tangentFrame_change c d m hc hd v).symm)
  have hk : LinearMap.ker J.toLinearMap = ⊥ := LinearMap.ker_eq_bot.mpr hi
  apply (Matrix.isUnit_iff_isUnit_det _).mpr
  apply isUnit_iff_ne_zero.mpr
  intro hz
  rw [det_derivativeMatrix] at hz
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz) hk

theorem pullback2_eq_pullbackMetric (A T : Matrix Index Index ℝ) :
    (TensorCoordinateChange.pullback2 A T : Matrix Index Index ℝ) =
      TensorCoordinateChange.pullbackMetric T A := by
  ext i j
  simp only [TensorCoordinateChange.pullback2_apply, TensorCoordinateChange.pullbackMetric,
    Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro a ha
  ring

def physicalNorm2 (r : Metric (M := M)) (B : Field (M := M)) (m : M) : ℝ :=
  norm2 (frameComponents r.inner m m) (frameComponents B m m)

theorem norm2_frame_independent (r : Metric (M := M)) (B : Field (M := M)) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source) :
    norm2 (frameComponents r.inner c m) (frameComponents B c m) =
      norm2 (frameComponents r.inner d m) (frameComponents B d m) := by
  rw [frameComponents_change r.inner c d m hc hd, frameComponents_change B c d m hc hd,
    ← pullback2_eq_pullbackMetric
      (derivativeMatrix (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)))
      (frameComponents B d m)]
  exact TensorCoordinateChange.norm2_pullback _ _ (transitionMatrix_isUnit c d m hc hd) _

theorem physicalNorm2_eq_frame (r : Metric (M := M)) (B : Field (M := M)) (c m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) :
    physicalNorm2 r B m = norm2 (frameComponents r.inner c m) (frameComponents B c m) :=
  (norm2_frame_independent r B c m m hc (mem_chart_source CoordinateSpace m)).symm

theorem physicalNorm2_eq_coordinate (r : Metric (M := M)) (B : Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    physicalNorm2 r B ((chartAt CoordinateSpace c).symm y) =
      norm2 (metricComponents (coordinateMetric r c) y) (metricComponents (coordinateBilinear B c) y) := by
  have hm := (chartAt CoordinateSpace c).symm_mapsTo hy
  have h := physicalNorm2_eq_frame r B c ((chartAt CoordinateSpace c).symm y) hm
  rw [frameComponents_eq_coordinate r.inner _ _ hm, frameComponents_eq_coordinate B _ _ hm,
    (chartAt CoordinateSpace c).right_inv hy] at h
  exact h


theorem frameComponents_inner_posDef (r : Metric (M := M)) (c m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) : (frameComponents r.inner c m).PosDef := by
  rw [frameComponents_eq_coordinate r.inner c m hc]
  exact ManifoldMetric.coordinateMetric_posDef r c ((chartAt CoordinateSpace c).map_source hc)

theorem physicalNorm2_eq_ofMatrix_norm (r : Metric (M := M)) (B : Field (M := M)) (m : M) :
    physicalNorm2 r B m = @Norm.norm ((Index × Index) → ℝ)
      (Matrix.NormedAddCommGroup.ofMatrix (gram2_posDef _
        (frameComponents_inner_posDef r m m (mem_chart_source CoordinateSpace m)))).toNorm
      (flatten2 (frameComponents B m m)) :=
  norm2_eq_ofMatrix_norm _
    (frameComponents_inner_posDef r m m (mem_chart_source CoordinateSpace m)) _

theorem physicalNorm2_nonneg (r : Metric (M := M)) (B : Field (M := M)) (m : M) :
    0 ≤ physicalNorm2 r B m := Real.sqrt_nonneg _


end Burnett.Geometry.ManifoldTensorNorm
