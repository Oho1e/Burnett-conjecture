import Burnett.Geometry.GlobalLeviCivita
import Burnett.Geometry.GlobalConnectionLaws
import Burnett.Geometry.CurvatureDifference

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.IntrinsicCurvature

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open ManifoldMetric ManifoldMetricTransition ChartVectorField ChartConnectionNaturality

def coordinateCurvature (Γ : CoordinateSpace → Connection)
    (X Y Z : CoordinateCovariantDerivative.VectorField) (y : CoordinateSpace) : CoordinateSpace :=
  CoordinateCovariantDerivative.derivative Γ X (CoordinateCovariantDerivative.derivative Γ Y Z) y -
    CoordinateCovariantDerivative.derivative Γ Y (CoordinateCovariantDerivative.derivative Γ X Z) y -
    CoordinateCovariantDerivative.derivative Γ (_root_.VectorField.lieBracket ℝ X Y) Z y

theorem derivative_congr_right_germ (Γ : CoordinateSpace → Connection)
    (X Z W : CoordinateCovariantDerivative.VectorField) (y : CoordinateSpace)
    (hZW : Z =ᶠ[𝓝 y] W) :
    CoordinateCovariantDerivative.derivative Γ X Z y =
      CoordinateCovariantDerivative.derivative Γ X W y := by
  unfold CoordinateCovariantDerivative.derivative
  rw [hZW.fderiv_eq, hZW.eq_of_nhds]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The actual iterated global connection and mathlib's actual manifold Lie bracket. -/
def curvature (B : ManifoldBilinear.Field (M := M)) (X Y Z : Field (M := M)) : Field (M := M) :=
  fun m => GlobalCovariantDerivative.derivative B X (GlobalCovariantDerivative.derivative B Y Z) m -
    GlobalCovariantDerivative.derivative B Y (GlobalCovariantDerivative.derivative B X Z) m -
    GlobalCovariantDerivative.derivative B (_root_.VectorField.mlieBracket Model X Y) Z m

theorem coordinateVector_sub (X Y : Field (M := M)) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (fun m => X m - Y m) c y = coordinateVector X c y - coordinateVector Y c y := by
  rw [ChartDifferential.coordinateVector_eq_mfderiv_chart (fun m => X m - Y m) c hy,
    ChartDifferential.coordinateVector_eq_mfderiv_chart X c hy,
    ChartDifferential.coordinateVector_eq_mfderiv_chart Y c hy]
  exact map_sub _ _ _

theorem isSmooth_sub (X Y : Field (M := M)) (hX : IsSmooth X) (hY : IsSmooth Y) :
    IsSmooth (fun m => X m - Y m) := by
  apply isSmooth_of_contDiffOn_coordinateVector
  intro c
  exact ((contDiffOn_coordinateVector X hX c).sub (contDiffOn_coordinateVector Y hY c)).congr
    (fun y hy => coordinateVector_sub X Y c hy)

theorem isSmooth_mlieBracket (X Y : Field (M := M)) (hX : IsSmooth X) (hY : IsSmooth Y) :
    IsSmooth (_root_.VectorField.mlieBracket Model X Y) := by
  apply isSmooth_of_contDiffOn_coordinateVector
  intro c
  have hU := (chartAt CoordinateSpace c).open_target
  have hx := contDiffOn_coordinateVector X hX c
  have hy := contDiffOn_coordinateVector Y hY c
  have hdx := (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hx |>.2
  have hdy := (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hy |>.2
  exact ((hdy.clm_apply hx).sub (hdx.clm_apply hy)).congr
    (fun y hy => ChartLieBracket.coordinateVector_mlieBracket X Y hX hY c hy)

theorem isSmooth_curvature (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z) : IsSmooth (curvature B X Y Z) := by
  have hYZ := GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND Y Z hY hZ
  have hXZ := GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND X Z hX hZ
  exact isSmooth_sub _ _
    (isSmooth_sub _ _
      (GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND X _ hX hYZ)
      (GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND Y _ hY hXZ))
    (GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND _ Z
      (isSmooth_mlieBracket X Y hX hY) hZ)

theorem coordinateVector_curvature (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (curvature B X Y Z) c y =
      coordinateCurvature (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (coordinateVector X c) (coordinateVector Y c) (coordinateVector Z c) y := by
  let Γ := BackgroundConnection.computedConnection (coordinateBilinear B c)
  have hYZ := GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND Y Z hY hZ
  have hXZ := GlobalCovariantDerivative.isSmooth_derivative B hB hSym hND X Z hX hZ
  have eYZ : coordinateVector (GlobalCovariantDerivative.derivative B Y Z) c =ᶠ[𝓝 y]
      CoordinateCovariantDerivative.derivative Γ (coordinateVector Y c) (coordinateVector Z c) := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hy] with z hz
    exact GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND Y Z hZ c hz
  have eXZ : coordinateVector (GlobalCovariantDerivative.derivative B X Z) c =ᶠ[𝓝 y]
      CoordinateCovariantDerivative.derivative Γ (coordinateVector X c) (coordinateVector Z c) := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hy] with z hz
    exact GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND X Z hZ c hz
  have e1 : coordinateDerivative B X (GlobalCovariantDerivative.derivative B Y Z) c y =
      CoordinateCovariantDerivative.derivative Γ (coordinateVector X c)
        (CoordinateCovariantDerivative.derivative Γ (coordinateVector Y c) (coordinateVector Z c)) y :=
    derivative_congr_right_germ Γ _ _ _ y eYZ
  have e2 : coordinateDerivative B Y (GlobalCovariantDerivative.derivative B X Z) c y =
      CoordinateCovariantDerivative.derivative Γ (coordinateVector Y c)
        (CoordinateCovariantDerivative.derivative Γ (coordinateVector X c) (coordinateVector Z c)) y :=
    derivative_congr_right_germ Γ _ _ _ y eXZ
  have e3 : coordinateDerivative B (_root_.VectorField.mlieBracket Model X Y) Z c y =
      CoordinateCovariantDerivative.derivative Γ
        (_root_.VectorField.lieBracket ℝ (coordinateVector X c) (coordinateVector Y c))
        (coordinateVector Z c) y := by
    unfold coordinateDerivative CoordinateCovariantDerivative.derivative
    rw [ChartLieBracket.coordinateVector_mlieBracket X Y hX hY c hy]
  change coordinateVector (fun m =>
    (GlobalCovariantDerivative.derivative B X (GlobalCovariantDerivative.derivative B Y Z) m -
      GlobalCovariantDerivative.derivative B Y (GlobalCovariantDerivative.derivative B X Z) m) -
      GlobalCovariantDerivative.derivative B (_root_.VectorField.mlieBracket Model X Y) Z m) c y = _
  rw [coordinateVector_sub _ _ c hy, coordinateVector_sub _ _ c hy,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND X _ hYZ c hy,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND Y _ hXZ c hy,
    GlobalCovariantDerivative.coordinateVector_derivative B hB hSym hND _ Z hZ c hy,
    e1, e2, e3]
  rfl

theorem curvature_eq_tangentFrame (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    curvature B X Y Z m = tangentFrame c m
      (coordinateCurvature (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (coordinateVector X c) (coordinateVector Y c) (coordinateVector Z c)
        (chartAt CoordinateSpace c m)) := by
  have hy := (chartAt CoordinateSpace c).mapsTo hm
  have h := coordinateVector_curvature B hB hSym hND X Y Z hX hY hZ c hy
  rw [coordinateVector_at_chart _ c m hm] at h
  rw [← h]
  exact (tangentFrame_frameVector _ c m hm).symm

end Burnett.Geometry.IntrinsicCurvature
