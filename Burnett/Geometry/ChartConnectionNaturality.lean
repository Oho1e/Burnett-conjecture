import Burnett.Geometry.ConnectionTermNaturality

/-!
# Actual coordinate affine operators agree on genuine chart overlaps

The connection coefficients come from the same smooth symmetric
nondegenerate bilinear field on actual tangent fibers. Vector fields use
the preferred tangent trivializations proved in ChartVectorField. Their
actual differentiated coordinate law and the genuine Christoffel law
cancel the same Hessian term, giving the transformation of the covariant
derivative and equality in one tangent fiber.

Only W needs smoothness in this pointwise naturality result: V occurs by
its value. No coordinate transformation, Hessian identity, or connection
naturality law is an input. Values outside chart sources are total-function
conventions. A global smooth affine operator and its Levi-Civita properties
are separate constructions; this file supplies the overlap agreement.
-/

noncomputable section
namespace Burnett.Geometry.ChartConnectionNaturality
open Bundle Set
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ChartVectorField
open Burnett.Geometry.BackgroundConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The existing actual coordinate affine derivative for one preferred chart. -/
def coordinateDerivative (B : ManifoldBilinear.Field (M := M))
    (V W : ChartVectorField.Field (M := M)) (c : M) : CoordinateSpace → CoordinateSpace :=
  CoordinateCovariantDerivative.derivative (computedConnection (coordinateBilinear B c))
    (coordinateVector V c) (coordinateVector W c)

/-- Its reconstruction in the actual tangent fiber, meaningful on the chart source. -/
def chartDerivative (B : ManifoldBilinear.Field (M := M))
    (V W : ChartVectorField.Field (M := M)) (c m : M) : TangentSpace Model m :=
  tangentFrame c m (coordinateDerivative B V W c (chartAt CoordinateSpace c m))

theorem coordinateDerivative_change (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hW : ChartVectorField.IsSmooth W) (c d : M) {x : CoordinateSpace}
    (hx : x ∈ (chartTransition c d).source) :
    fderiv ℝ (chartTransition c d) x (coordinateDerivative B V W c x) =
      coordinateDerivative B V W d (chartTransition c d x) := by
  unfold coordinateDerivative CoordinateCovariantDerivative.derivative
  rw [map_add, ConnectionTermNaturality.coordinateBilinear_connectionTerm_change
    B hB hSym hND c d x hx]
  rw [coordinateVector_change V c d hx, coordinateVector_change W c d hx]
  rw [derivative_coordinateVector_change W hW c d hx (coordinateVector V c x)]
  abel

theorem tangentFrame_coordinateDerivative_change (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hW : ChartVectorField.IsSmooth W) (c d : M) {x : CoordinateSpace}
    (hx : x ∈ (chartTransition c d).source) :
    tangentFrame c ((chartAt CoordinateSpace c).symm x) (coordinateDerivative B V W c x) =
      tangentFrame d ((chartAt CoordinateSpace c).symm x)
        (coordinateDerivative B V W d (chartTransition c d x)) := by
  rw [tangentFrame_change_coordinates c d hx,
    coordinateDerivative_change B hB hSym hND V W hW c d hx]

theorem chartDerivative_eq (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hW : ChartVectorField.IsSmooth W) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source)
    (hd : m ∈ (chartAt CoordinateSpace d).source) :
    chartDerivative B V W c m = chartDerivative B V W d m := by
  have hx : chartAt CoordinateSpace c m ∈ (chartTransition c d).source := by
    change chartAt CoordinateSpace c m ∈ (chartAt CoordinateSpace c).target ∧
      (chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c m) ∈
        (chartAt CoordinateSpace d).source
    exact ⟨(chartAt CoordinateSpace c).mapsTo hc,
      by rw [(chartAt CoordinateSpace c).left_inv hc]; exact hd⟩
  have hφ : chartTransition c d (chartAt CoordinateSpace c m) = chartAt CoordinateSpace d m := by
    change chartAt CoordinateSpace d ((chartAt CoordinateSpace c).symm (chartAt CoordinateSpace c m)) = _
    rw [(chartAt CoordinateSpace c).left_inv hc]
  unfold chartDerivative
  calc
    _ = tangentFrame d m (fderiv ℝ (chartTransition c d) (chartAt CoordinateSpace c m)
        (coordinateDerivative B V W c (chartAt CoordinateSpace c m))) :=
      tangentFrame_change c d m hc hd _
    _ = _ := congrArg (tangentFrame d m) (by
      simpa only [hφ] using coordinateDerivative_change B hB hSym hND V W hW c d hx)

theorem coordinateMetricDerivative_change (r : Metric (M := M))
    (V W : ChartVectorField.Field (M := M)) (hW : ChartVectorField.IsSmooth W)
    (c d : M) {x : CoordinateSpace} (hx : x ∈ (chartTransition c d).source) :
    fderiv ℝ (chartTransition c d) x (coordinateDerivative r.inner V W c x) =
      coordinateDerivative r.inner V W d (chartTransition c d x) := by
  apply coordinateDerivative_change r.inner (ManifoldBilinear.isSmooth_inner r)
    (fun m u v => r.symm m u v) ?_ V W hW c d hx
  intro m u hu
  by_contra hne
  exact (ne_of_gt (r.pos m u hne)) (hu u)

end Burnett.Geometry.ChartConnectionNaturality
