import Burnett.Geometry.GlobalCovariantDerivative
import Burnett.Geometry.ChartDifferential
import Burnett.Geometry.AffineConnection
import Burnett.Geometry.ChartLieBracket

/-!
# The global metric connection preserves its metric and has zero torsion

The pairing is the actual evaluation of a smooth tangent-fiber bilinear
section on two genuine vector fields. The manifold scalar differential is
transported through the true chart and an open-target germ. The proved
coordinate compatibility then gives the global metric compatibility law.
Torsion is compared with mathlib's actual manifold Lie bracket using its
proved chart transport, never with a newly defined commutator.

These properties hold for smooth symmetric nondegenerate fields, including
indefinite ones. The original auxiliary Riemannian metric is instantiated
from its actual smoothness, symmetry and positivity. Affine connection
laws are proved separately in GlobalConnectionLaws. No uniqueness over an
abstract class of all global operators, intrinsic cov2 tensor derivative,
physical norm or complete Lorentz admissibility is claimed here.
-/

noncomputable section
namespace Burnett.Geometry.GlobalLeviCivita
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ManifoldMetricTransition
open Burnett.Geometry.ChartVectorField Burnett.Geometry.ChartDifferential
open Burnett.Geometry.ChartConnectionNaturality

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem contMDiff_pairing (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (U W : Field (M := M))
    (hU : IsSmooth U) (hW : IsSmooth W) :
    ContMDiff Model 𝓘(ℝ, ℝ) ∞ (fun m => B m (U m) (W m)) := by
  intro m
  have h := (hB.clm_bundle_apply₂ hU hW) m
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

theorem pairing_eq_coordinate (B : ManifoldBilinear.Field (M := M))
    (U W : Field (M := M)) (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    B m (U m) (W m) = coordinateBilinear B c (chartAt CoordinateSpace c m)
      (coordinateVector U c (chartAt CoordinateSpace c m))
      (coordinateVector W c (chartAt CoordinateSpace c m)) := by
  simp only [coordinateBilinear, coordinateVector, (chartAt CoordinateSpace c).left_inv hm]
  change B m (U m) (W m) =
    B m (tangentFrame c m (frameVector U c m)) (tangentFrame c m (frameVector W c m))
  rw [tangentFrame_frameVector U c m hm, tangentFrame_frameVector W c m hm]

theorem pairing_comp_chart_symm (B : ManifoldBilinear.Field (M := M))
    (U W : Field (M := M)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    B ((chartAt CoordinateSpace c).symm y) (U ((chartAt CoordinateSpace c).symm y))
        (W ((chartAt CoordinateSpace c).symm y)) =
      coordinateBilinear B c y (coordinateVector U c y) (coordinateVector W c y) := by
  change _ = B ((chartAt CoordinateSpace c).symm y)
    (tangentFrame c ((chartAt CoordinateSpace c).symm y) (coordinateVector U c y))
    (tangentFrame c ((chartAt CoordinateSpace c).symm y) (coordinateVector W c y))
  rw [tangentFrame_coordinateVector U c hy, tangentFrame_coordinateVector W c hy]

theorem derivative_metric_compatible (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V U W : Field (M := M))
    (hU : IsSmooth U) (hW : IsSmooth W) (m : M) :
    mfderiv Model 𝓘(ℝ, ℝ) (fun n => B n (U n) (W n)) m (V m) =
      B m (GlobalCovariantDerivative.derivative B V U m) (W m) +
        B m (U m) (GlobalCovariantDerivative.derivative B V W m) := by
  let c := m
  let x := chartAt CoordinateSpace c m
  have hm : m ∈ (chartAt CoordinateSpace c).source := mem_chart_source _ m
  have hx : x ∈ (chartAt CoordinateSpace c).target := (chartAt CoordinateSpace c).mapsTo hm
  have hf : MDifferentiableAt Model 𝓘(ℝ, ℝ) (fun n => B n (U n) (W n)) m :=
    ((contMDiff_pairing B hB U W hU hW) m).mdifferentiableAt (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have heq : ((fun n => B n (U n) (W n)) ∘ (chartAt CoordinateSpace c).symm) =ᶠ[𝓝 x]
      (fun y => coordinateBilinear B c y (coordinateVector U c y) (coordinateVector W c y)) := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hx] with y hy
    exact pairing_comp_chart_symm B U W c hy
  have hg : DifferentiableComponentsAt
      (metricComponents (coordinateBilinear B c)) x := by
    intro i j
    apply ((ManifoldBilinear.contDiffOn_metricComponents B hB c i j).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hx)).differentiableAt
    change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  have hcomp := AffineConnection.computed_derivative_metric_compatible (coordinateBilinear B c)
    (coordinateVector V c) (coordinateVector U c) (coordinateVector W c) x
    (ManifoldBilinear.coordinateBilinear_nondegenerate B hND c hx)
    (ManifoldBilinear.eventually_coordinateBilinear_symmetric B hSym c x) hg
    (differentiableAt_coordinateVector U hU c hx) (differentiableAt_coordinateVector W hW c hx)
  rw [scalar_mfderiv_eq_chart _ V c m hm hf, ← coordinateVector_at_chart V c m hm]
  rw [heq.fderiv_eq, hcomp]
  rw [pairing_eq_coordinate B (GlobalCovariantDerivative.derivative B V U) W c m hm,
    pairing_eq_coordinate B U (GlobalCovariantDerivative.derivative B V W) c m hm,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND V U hU c hx,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND V W hW c hx]
  rfl

theorem derivative_torsion_free (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : Field (M := M))
    (hV : IsSmooth V) (hW : IsSmooth W) (m : M) :
    GlobalCovariantDerivative.derivative B V W m - GlobalCovariantDerivative.derivative B W V m =
      _root_.VectorField.mlieBracket Model V W m := by
  let c := m
  have hm : m ∈ (chartAt CoordinateSpace c).source := mem_chart_source _ m
  rw [GlobalCovariantDerivative.derivative_eq_chart B hB hSym hND V W hW c m hm,
    GlobalCovariantDerivative.derivative_eq_chart B hB hSym hND W V hV c m hm,
    ChartLieBracket.mlieBracket_eq_tangentFrame V W hV hW c m hm]
  change tangentFrame c m (coordinateDerivative B V W c (chartAt CoordinateSpace c m)) -
    tangentFrame c m (coordinateDerivative B W V c (chartAt CoordinateSpace c m)) = _
  rw [← map_sub]
  exact congrArg (tangentFrame c m) (AffineConnection.computed_derivative_torsion_free
    (coordinateBilinear B c) (coordinateVector V c) (coordinateVector W c)
    (chartAt CoordinateSpace c m)
    (ManifoldBilinear.eventually_coordinateBilinear_symmetric B hSym c _))

theorem inner_nondegenerate (r : Metric (M := M)) :
    ManifoldBilinear.IsNondegenerate r.inner := by
  intro m u hu
  by_contra hn
  exact (ne_of_gt (r.pos m u hn)) (hu u)

theorem metric_derivative_isSmooth (r : Metric (M := M)) (V W : Field (M := M))
    (hV : IsSmooth V) (hW : IsSmooth W) :
    IsSmooth (GlobalCovariantDerivative.derivative r.inner V W) :=
  GlobalCovariantDerivative.isSmooth_derivative r.inner (ManifoldBilinear.isSmooth_inner r)
    r.symm (inner_nondegenerate r) V W hV hW

theorem metric_derivative_compatible (r : Metric (M := M)) (V U W : Field (M := M))
    (hU : IsSmooth U) (hW : IsSmooth W) (m : M) :
    mfderiv Model 𝓘(ℝ, ℝ) (fun n => r.inner n (U n) (W n)) m (V m) =
      r.inner m (GlobalCovariantDerivative.derivative r.inner V U m) (W m) +
        r.inner m (U m) (GlobalCovariantDerivative.derivative r.inner V W m) :=
  derivative_metric_compatible r.inner (ManifoldBilinear.isSmooth_inner r)
    r.symm (inner_nondegenerate r) V U W hU hW m

theorem metric_derivative_torsion_free (r : Metric (M := M)) (V W : Field (M := M))
    (hV : IsSmooth V) (hW : IsSmooth W) (m : M) :
    GlobalCovariantDerivative.derivative r.inner V W m -
      GlobalCovariantDerivative.derivative r.inner W V m =
      _root_.VectorField.mlieBracket Model V W m :=
  derivative_torsion_free r.inner (ManifoldBilinear.isSmooth_inner r)
    r.symm (inner_nondegenerate r) V W hV hW m

end Burnett.Geometry.GlobalLeviCivita
