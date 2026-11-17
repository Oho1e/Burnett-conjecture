import Burnett.Geometry.ChartDifferential
import Mathlib.Geometry.Manifold.VectorField.LieBracket

/-!
# The actual intrinsic Lie bracket in preferred tangent coordinates

Mathlib's manifold mlieBracket is transported along the genuine inverse
chart using its proved pullback naturality. The inverse manifold derivative
is identified with the real forward tangent coordinates on the chart target.
Open-target germ congruence then identifies the result with the genuine
Banach-space lieBracket of the existing coordinate vector fields.
No custom commutator or bracket transformation law is an input.
-/

noncomputable section
namespace Burnett.Geometry.ChartLieBracket
open Bundle Set Filter
open scoped Manifold ContDiff Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ChartVectorField Burnett.Geometry.ChartDifferential

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem inverse_mfderiv_chart_symm (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    (mfderiv Model Model (chartAt CoordinateSpace c).symm y).inverse =
      mfderiv Model Model (chartAt CoordinateSpace c) ((chartAt CoordinateSpace c).symm y) := by
  have hy' : y ∈ (extChartAt Model c).target := by simpa only [Model, mfld_simps] using hy
  have h := ContinuousLinearMap.inverse_eq
    (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := Model) hy')
    (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := Model) hy')
  simpa only [Model, mfld_simps, mfderivWithin_univ] using h

theorem mpullback_chart_symm_eq_coordinateVector (V : Field (M := M)) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    _root_.VectorField.mpullback (M := CoordinateSpace) (M' := M) Model Model (chartAt CoordinateSpace c).symm V y =
      coordinateVector V c y := by
  rw [_root_.VectorField.mpullback_apply, inverse_mfderiv_chart_symm c hy]
  exact (coordinateVector_eq_mfderiv_chart V c hy).symm

theorem mlieBracket_model_eq_lieBracket (V W : CoordinateSpace → CoordinateSpace) (x : CoordinateSpace) :
    _root_.VectorField.mlieBracket Model V W x = _root_.VectorField.lieBracket (E := CoordinateSpace) ℝ V W x := by
  rw [_root_.VectorField.mlieBracket, _root_.VectorField.mlieBracketWithin_eq_lieBracketWithin,
    _root_.VectorField.lieBracketWithin_univ]

theorem coordinateVector_mlieBracket (V W : Field (M := M))
    (hV : IsSmooth V) (hW : IsSmooth W) (c : M) {y : CoordinateSpace}
    (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (_root_.VectorField.mlieBracket Model V W) c y =
      _root_.VectorField.lieBracket (E := CoordinateSpace) ℝ (coordinateVector V c) (coordinateVector W c) y := by
  have hVm : MDifferentiableAt Model Model.tangent
      (fun m => (V m : TangentBundle Model M)) ((chartAt CoordinateSpace c).symm y) :=
    (hV _).mdifferentiableAt (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hWm : MDifferentiableAt Model Model.tangent
      (fun m => (W m : TangentBundle Model M)) ((chartAt CoordinateSpace c).symm y) :=
    (hW _).mdifferentiableAt (by
      change ((1 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  have hi : ContMDiffAt Model Model ∞ (chartAt CoordinateSpace c).symm y :=
    (show ContMDiffOn Model Model ∞ (chartAt CoordinateSpace c).symm
      (chartAt CoordinateSpace c).target from contMDiffOn_chart_symm).contMDiffAt
        ((chartAt CoordinateSpace c).open_target.mem_nhds hy)
  have hn : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
    norm_num
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  letI : IsManifold Model (minSmoothness ℝ 2) M := IsManifold.of_le (n := ∞) hn
  have hb := _root_.VectorField.mpullback_mlieBracket (M := CoordinateSpace) (M' := M) (I := Model) (I' := Model)
    (x₀ := y) hVm hWm hi hn
  have hvEq : _root_.VectorField.mpullback (M := CoordinateSpace) (M' := M) Model Model (chartAt CoordinateSpace c).symm V =ᶠ[𝓝 y]
      coordinateVector V c := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hy] with z hz
    exact mpullback_chart_symm_eq_coordinateVector V c hz
  have hwEq : _root_.VectorField.mpullback (M := CoordinateSpace) (M' := M) Model Model (chartAt CoordinateSpace c).symm W =ᶠ[𝓝 y]
      coordinateVector W c := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hy] with z hz
    exact mpullback_chart_symm_eq_coordinateVector W c hz
  calc
    _ = _root_.VectorField.mpullback (M := CoordinateSpace) (M' := M) Model Model (chartAt CoordinateSpace c).symm
        (_root_.VectorField.mlieBracket Model V W) y :=
      (mpullback_chart_symm_eq_coordinateVector _ c hy).symm
    _ = _ := hb
    _ = _root_.VectorField.lieBracket (E := CoordinateSpace) ℝ
        (_root_.VectorField.mpullback (M := CoordinateSpace) (M' := M) Model Model (chartAt CoordinateSpace c).symm V)
        (_root_.VectorField.mpullback (M := CoordinateSpace) (M' := M) Model Model (chartAt CoordinateSpace c).symm W) y :=
      mlieBracket_model_eq_lieBracket _ _ y
    _ = _ := hvEq.lieBracket_vectorField_eq hwEq

theorem frameVector_mlieBracket (V W : Field (M := M))
    (hV : IsSmooth V) (hW : IsSmooth W) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    frameVector (_root_.VectorField.mlieBracket Model V W) c m =
      _root_.VectorField.lieBracket (E := CoordinateSpace) ℝ (coordinateVector V c) (coordinateVector W c)
        (chartAt CoordinateSpace c m) := by
  have h := coordinateVector_mlieBracket V W hV hW c ((chartAt CoordinateSpace c).mapsTo hm)
  rw [coordinateVector_at_chart _ c m hm] at h
  exact h

theorem mlieBracket_eq_tangentFrame (V W : Field (M := M))
    (hV : IsSmooth V) (hW : IsSmooth W) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    _root_.VectorField.mlieBracket Model V W m =
      tangentFrame c m (_root_.VectorField.lieBracket (E := CoordinateSpace) ℝ (coordinateVector V c)
        (coordinateVector W c) (chartAt CoordinateSpace c m)) := by
  rw [← frameVector_mlieBracket V W hV hW c m hm, tangentFrame_frameVector]
  exact hm

end Burnett.Geometry.ChartLieBracket
