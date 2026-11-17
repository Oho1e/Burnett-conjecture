import Burnett.Geometry.ManifoldBilinear
import Burnett.Geometry.AffineConnection

/-!
# Actual smooth chart transitions and their symmetric second derivative

The Hessian is the actual iterated Frechet derivative of the preferred
chart transition. Its lower-slot symmetry follows from the smooth atlas
on the open overlap, without a globally smooth total extension.
-/
noncomputable section
namespace Burnett.Geometry.ActualChartSecondJet
open scoped Manifold ContDiff
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ChartVolume

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem contDiffOn_chartTransition_infty (c d : M) :
    ContDiffOn ℝ ∞ (chartTransition c d) (chartTransition c d).source := by
  have h : (chartAt CoordinateSpace c).symm.trans (chartAt CoordinateSpace d) ∈
      contDiffGroupoid ∞ Model :=
    HasGroupoid.compatible (chart_mem_atlas CoordinateSpace c) (chart_mem_atlas CoordinateSpace d)
  have h' := h.1
  change ContDiffOn ℝ ∞ _ _ at h'
  simpa only [mfld_simps, chartTransition] using h'

def actualHessian (c d : M) (x : CoordinateSpace) : Connection :=
  fun a b e => ((fderiv ℝ (fderiv ℝ (chartTransition c d)) x (coordinateBasis b))
    (coordinateBasis e)) a

theorem actualHessian_symmetric (c d : M) (x : CoordinateSpace)
    (hx : x ∈ (chartTransition c d).source) (a b e : Index) :
    actualHessian c d x a b e = actualHessian c d x a e b := by
  have hc := (contDiffOn_chartTransition_infty c d).contDiffAt
    ((chartTransition c d).open_source.mem_nhds hx)
  have hs := hc.isSymmSndFDerivAt (by
    norm_num
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun z : CoordinateSpace => z a) (hs.eq (coordinateBasis b) (coordinateBasis e))

end Burnett.Geometry.ActualChartSecondJet
