import Burnett.Geometry.ChartConnectionNaturality
import Burnett.Geometry.SmoothMetricConnection

/-!
# A global derivative from genuine preferred-chart affine operators

At m the total definition uses the chart centered at m. For a genuine smooth
symmetric nondegenerate fiberwise bilinear field and smooth W, overlap
naturality proves equality with every preferred chart containing m. This
is a tangent-bundle section, not a vector in a globally identified frame.

Smoothness is proved from the actual coordinate formula: the computed
Christoffel field is smooth by its matrix-inverse and derivative construction,
and Frechet differentiation and finite contraction preserve coordinate
smoothness. The genuine total-space section is then smooth by the proved
preferred-chart characterization. No supplied chart law or closure field
is part of the principal theorem.

The affine laws, global metric compatibility, torsion and Levi-Civita
characterization are separate consumers of this constructor. No manifold
measure or physical tensor-norm instance is introduced here.
-/

noncomputable section
namespace Burnett.Geometry.GlobalCovariantDerivative
open Bundle Set
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetricTransition Burnett.Geometry.ChartVectorField
open Burnett.Geometry.ChartConnectionNaturality Burnett.Geometry.BackgroundConnection

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The chart centered at each point gives a total genuine tangent section. -/
def derivative (B : ManifoldBilinear.Field (M := M))
    (V W : ChartVectorField.Field (M := M)) : ChartVectorField.Field (M := M) :=
  fun m => chartDerivative B V W m m

/-- Under the geometric hypotheses this value agrees with any preferred chart. -/
theorem derivative_eq_chart (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hW : ChartVectorField.IsSmooth W) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    derivative B V W m = chartDerivative B V W c m :=
  chartDerivative_eq B hB hSym hND V W hW m c m (mem_chart_source CoordinateSpace m) hm

theorem coordinateVector_derivative (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hW : ChartVectorField.IsSmooth W) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (derivative B V W) c y = coordinateDerivative B V W c y := by
  let m := (chartAt CoordinateSpace c).symm y
  have hm : m ∈ (chartAt CoordinateSpace c).source := (chartAt CoordinateSpace c).symm_mapsTo hy
  apply tangentFrame_injective c m hm
  calc
    _ = derivative B V W m := tangentFrame_coordinateVector (derivative B V W) c hy
    _ = chartDerivative B V W c m := derivative_eq_chart B hB hSym hND V W hW c m hm
    _ = _ := by
      change tangentFrame c m (coordinateDerivative B V W c (chartAt CoordinateSpace c m)) = _
      change tangentFrame c m (coordinateDerivative B V W c
        (chartAt CoordinateSpace c ((chartAt CoordinateSpace c).symm y))) = _
      rw [(chartAt CoordinateSpace c).right_inv hy]

omit [IsManifold Model ∞ M] in
theorem contDiffOn_connectionTerm {U : Set CoordinateSpace}
    (Γ : CoordinateSpace → Connection) (V W : CoordinateSpace → CoordinateSpace)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) :
    ContDiffOn ℝ ∞ (fun x => CoordinateCovariantDerivative.connectionTerm (Γ x) (V x) (W x)) U := by
  have hg (a b c : Index) : ContDiffOn ℝ ∞ (fun x => Γ x a b c) U :=
    contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) c
  have hv (i : Index) : ContDiffOn ℝ ∞ (fun x => V x i) U := by
    change ContDiffOn ℝ ∞ ((EuclideanSpace.proj i : CoordinateSpace →L[ℝ] ℝ) ∘ V) U
    exact ContDiffOn.continuousLinearMap_comp _ hV
  have hw (i : Index) : ContDiffOn ℝ ∞ (fun x => W x i) U := by
    change ContDiffOn ℝ ∞ ((EuclideanSpace.proj i : CoordinateSpace →L[ℝ] ℝ) ∘ W) U
    exact ContDiffOn.continuousLinearMap_comp _ hW
  have hf : ContDiffOn ℝ ∞ (fun x => fun a => ∑ b, ∑ c, Γ x a b c * V x b * W x c) U := by
    apply contDiffOn_pi.mpr
    intro a
    exact ContDiffOn.sum (fun b _ => ContDiffOn.sum (fun c _ => ((hg a b c).mul (hv b)).mul (hw c)))
  exact hf.continuousLinearMap_comp (EuclideanSpace.equiv Index ℝ).symm.toContinuousLinearMap

omit [IsManifold Model ∞ M] in
theorem contDiffOn_coordinateAffineDerivative {U : Set CoordinateSpace} (hU : IsOpen U)
    (Γ : CoordinateSpace → Connection) (V W : CoordinateSpace → CoordinateSpace)
    (hΓ : ContDiffOn ℝ ∞ Γ U) (hV : ContDiffOn ℝ ∞ V U) (hW : ContDiffOn ℝ ∞ W U) :
    ContDiffOn ℝ ∞ (CoordinateCovariantDerivative.derivative Γ V W) U := by
  have hdW := (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hW |>.2
  exact (hdW.clm_apply hV).add (contDiffOn_connectionTerm Γ V W hΓ hV hW)

theorem contDiffOn_coordinateDerivative_of_connection (B : ManifoldBilinear.Field (M := M))
    (V W : ChartVectorField.Field (M := M)) (hV : ChartVectorField.IsSmooth V)
    (hW : ChartVectorField.IsSmooth W) (c : M)
    (hΓ : ContDiffOn ℝ ∞ (computedConnection (coordinateBilinear B c))
      (chartAt CoordinateSpace c).target) :
    ContDiffOn ℝ ∞ (coordinateDerivative B V W c) (chartAt CoordinateSpace c).target :=
  contDiffOn_coordinateAffineDerivative (chartAt CoordinateSpace c).open_target
    _ _ _ hΓ (contDiffOn_coordinateVector V hV c) (contDiffOn_coordinateVector W hW c)

theorem isSmooth_derivative_of_coordinate_connections (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hV : ChartVectorField.IsSmooth V) (hW : ChartVectorField.IsSmooth W)
    (hΓ : ∀ c : M, ContDiffOn ℝ ∞ (computedConnection (coordinateBilinear B c))
      (chartAt CoordinateSpace c).target) : ChartVectorField.IsSmooth (derivative B V W) := by
  apply isSmooth_of_contDiffOn_coordinateVector
  intro c
  exact (contDiffOn_coordinateDerivative_of_connection B V W hV hW c (hΓ c)).congr
    (fun y hy => coordinateVector_derivative B hB hSym hND V W hW c hy)

/-- Actual smoothness closure; coordinate Christoffel regularity is derived, not assumed. -/
theorem isSmooth_derivative (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (V W : ChartVectorField.Field (M := M))
    (hV : ChartVectorField.IsSmooth V) (hW : ChartVectorField.IsSmooth W) :
    ChartVectorField.IsSmooth (derivative B V W) :=
  isSmooth_derivative_of_coordinate_connections B hB hSym hND V W hV hW
    (fun c => SmoothMetricConnection.contDiffOn_coordinateBilinear_connection B hB hND c)

end Burnett.Geometry.GlobalCovariantDerivative
