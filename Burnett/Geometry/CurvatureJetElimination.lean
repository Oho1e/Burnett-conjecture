import Burnett.Geometry.IntrinsicCurvature

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.CurvatureJetElimination

open Filter Set
open scoped BigOperators Topology Manifold ContDiff
open Burnett.RicciSymbol
open ConnectionDifference CurvatureDifference CoordinateCovariantDerivative

def directionalConnection (Γ : CoordinateSpace → Connection) (y v : CoordinateSpace) : Connection :=
  fun a b c => fderiv ℝ (fun z => Γ z a b c) y v

theorem differentiableAt_connectionTerm (Γ : CoordinateSpace → Connection) (X Z : VectorField)
    (y : CoordinateSpace) (hΓ : DifferentiableConnectionAt Γ y)
    (hX : DifferentiableAt ℝ X y) (hZ : DifferentiableAt ℝ Z y) :
    DifferentiableAt ℝ (fun z => connectionTerm (Γ z) (X z) (Z z)) y := by
  apply (differentiableAt_piLp 2).mpr
  intro a
  simp only [connectionTerm_apply]
  exact DifferentiableAt.fun_sum (u := Finset.univ) (fun b _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun c _ =>
      ((hΓ a b c).fun_mul (AffineConnection.component_differentiable hX b)).fun_mul
        (AffineConnection.component_differentiable hZ c)))

theorem fderiv_connectionTerm (Γ : CoordinateSpace → Connection) (X Z : VectorField)
    (y v : CoordinateSpace) (hΓ : DifferentiableConnectionAt Γ y)
    (hX : DifferentiableAt ℝ X y) (hZ : DifferentiableAt ℝ Z y) :
    fderiv ℝ (fun z => connectionTerm (Γ z) (X z) (Z z)) y v =
      connectionTerm (Γ y) (fderiv ℝ X y v) (Z y) +
        connectionTerm (directionalConnection Γ y v) (X y) (Z y) +
        connectionTerm (Γ y) (X y) (fderiv ℝ Z y v) := by
  have hf := differentiableAt_connectionTerm Γ X Z y hΓ hX hZ
  have hx (b : Index) := AffineConnection.component_differentiable hX b
  have hz (c : Index) := AffineConnection.component_differentiable hZ c
  ext a
  rw [← AffineConnection.fderiv_component hf a v]
  simp only [connectionTerm_apply]
  have ht (b c : Index) := ((hΓ a b c).fun_mul (hx b)).fun_mul (hz c)
  rw [fderiv_fun_sum (u := Finset.univ) (fun b _ =>
    DifferentiableAt.fun_sum (u := Finset.univ) (fun c _ => ht b c))]
  simp only [ContinuousLinearMap.sum_apply]
  simp_rw [fderiv_fun_sum (u := Finset.univ) (fun c _ => ht _ c), ContinuousLinearMap.sum_apply]
  simp_rw [AffineConnection.fderiv_product3 _ _ _ y v (hΓ a _ _) (hx _) (hz _),
    AffineConnection.fderiv_component hX, AffineConnection.fderiv_component hZ]
  simp only [PiLp.add_apply, connectionTerm_apply, directionalConnection, Finset.sum_add_distrib]
  ring

theorem fderiv_directionalField (Z Y : VectorField) (y v : CoordinateSpace)
    (hDZ : DifferentiableAt ℝ (fderiv ℝ Z) y) (hY : DifferentiableAt ℝ Y y) :
    fderiv ℝ (fun z => fderiv ℝ Z z (Y z)) y v =
      fderiv ℝ Z y (fderiv ℝ Y y v) + fderiv ℝ (fderiv ℝ Z) y v (Y y) := by
  rw [fderiv_clm_apply hDZ hY]
  rfl

def curvatureValue (Γ : Connection) (dΓ : CoordinateSpace → Connection)
    (u v w : CoordinateSpace) : CoordinateSpace :=
  connectionTerm (dΓ u) v w - connectionTerm (dΓ v) u w +
    connectionTerm Γ u (connectionTerm Γ v w) - connectionTerm Γ v (connectionTerm Γ u w)

theorem coordinateCurvature_eq_curvatureValue (Γ : CoordinateSpace → Connection) (X Y Z : VectorField)
    (y : CoordinateSpace) (hΓ : DifferentiableConnectionAt Γ y)
    (hX : DifferentiableAt ℝ X y) (hY : DifferentiableAt ℝ Y y)
    (hZ : ContDiffAt ℝ 2 Z y) :
    IntrinsicCurvature.coordinateCurvature Γ X Y Z y =
      curvatureValue (Γ y) (directionalConnection Γ y) (X y) (Y y) (Z y) := by
  have hz : DifferentiableAt ℝ Z y := hZ.differentiableAt (by norm_num)
  have hdz : DifferentiableAt ℝ (fderiv ℝ Z) y :=
    (hZ.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)).differentiableAt le_rfl
  have hsym : IsSymmSndFDerivAt ℝ Z y := hZ.isSymmSndFDerivAt (by norm_num)
  have hdY (v : CoordinateSpace) : fderiv ℝ (derivative Γ Y Z) y v =
      (fderiv ℝ Z y (fderiv ℝ Y y v) + fderiv ℝ (fderiv ℝ Z) y v (Y y)) +
        (connectionTerm (Γ y) (fderiv ℝ Y y v) (Z y) +
          connectionTerm (directionalConnection Γ y v) (Y y) (Z y) +
          connectionTerm (Γ y) (Y y) (fderiv ℝ Z y v)) := by
    change fderiv ℝ (fun z => fderiv ℝ Z z (Y z) + connectionTerm (Γ z) (Y z) (Z z)) y v = _
    rw [fderiv_fun_add (hdz.clm_apply hY) (differentiableAt_connectionTerm Γ Y Z y hΓ hY hz),
      ContinuousLinearMap.add_apply, fderiv_directionalField Z Y y v hdz hY,
      fderiv_connectionTerm Γ Y Z y v hΓ hY hz]
  have hdX (v : CoordinateSpace) : fderiv ℝ (derivative Γ X Z) y v =
      (fderiv ℝ Z y (fderiv ℝ X y v) + fderiv ℝ (fderiv ℝ Z) y v (X y)) +
        (connectionTerm (Γ y) (fderiv ℝ X y v) (Z y) +
          connectionTerm (directionalConnection Γ y v) (X y) (Z y) +
          connectionTerm (Γ y) (X y) (fderiv ℝ Z y v)) := by
    change fderiv ℝ (fun z => fderiv ℝ Z z (X z) + connectionTerm (Γ z) (X z) (Z z)) y v = _
    rw [fderiv_fun_add (hdz.clm_apply hX) (differentiableAt_connectionTerm Γ X Z y hΓ hX hz),
      ContinuousLinearMap.add_apply, fderiv_directionalField Z X y v hdz hX,
      fderiv_connectionTerm Γ X Z y v hΓ hX hz]
  have hsub (u v w : CoordinateSpace) : connectionTerm (Γ y) (u-v) w =
      connectionTerm (Γ y) u w - connectionTerm (Γ y) v w := by
    change ConnectionTermNaturality.connectionBilinear (Γ y) (u-v) w = _
    rw [map_sub, LinearMap.sub_apply]
    rfl
  change (fderiv ℝ (derivative Γ Y Z) y (X y) + connectionTerm (Γ y) (X y) (derivative Γ Y Z y)) -
    (fderiv ℝ (derivative Γ X Z) y (Y y) + connectionTerm (Γ y) (Y y) (derivative Γ X Z y)) -
    (fderiv ℝ Z y (_root_.VectorField.lieBracket ℝ X Y y) +
      connectionTerm (Γ y) (_root_.VectorField.lieBracket ℝ X Y y) (Z y)) = _
  rw [hdY, hdX]
  simp only [derivative, _root_.VectorField.lieBracket, map_sub, connectionTerm_add_right, hsub]
  rw [hsym (X y) (Y y)]
  unfold curvatureValue
  abel

section Global

open ManifoldMetric ManifoldMetricTransition ChartVectorField

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem coordinateVector_curvature_eq_value (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z) (c : M)
    {y : CoordinateSpace} (hy : y ∈ (chartAt CoordinateSpace c).target) :
    coordinateVector (IntrinsicCurvature.curvature B X Y Z) c y =
      curvatureValue (BackgroundConnection.computedConnection (coordinateBilinear B c) y)
        (directionalConnection (BackgroundConnection.computedConnection (coordinateBilinear B c)) y)
        (coordinateVector X c y) (coordinateVector Y c y) (coordinateVector Z c y) := by
  rw [IntrinsicCurvature.coordinateVector_curvature B hB hSym hND X Y Z hX hY hZ c hy]
  have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection B hB hND c
  apply coordinateCurvature_eq_curvatureValue
  · intro a b d
    exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).differentiableAt (by simp)
  · exact differentiableAt_coordinateVector X hX c hy
  · exact differentiableAt_coordinateVector Y hY c hy
  · exact ((contDiffOn_coordinateVector Z hZ c).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds hy)).of_le (by
        change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact WithTop.coe_le_coe.mpr le_top)

theorem coordinateVector_eq_of_value (X Y : Field (M := M)) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) (h : X m = Y m) :
    coordinateVector X c (chartAt CoordinateSpace c m) =
      coordinateVector Y c (chartAt CoordinateSpace c m) := by
  rw [coordinateVector_at_chart X c m hm, coordinateVector_at_chart Y c m hm]
  unfold frameVector
  rw [h]

/-- Among genuine smooth extensions, R at m depends only on the three fiber values.
    This theorem does not assume or construct a global frame or extension of every fiber value. -/
theorem curvature_eq_of_values (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z X' Y' Z' : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z)
    (hX' : IsSmooth X') (hY' : IsSmooth Y') (hZ' : IsSmooth Z')
    (m : M) (hx : X m = X' m) (hy : Y m = Y' m) (hz : Z m = Z' m) :
    IntrinsicCurvature.curvature B X Y Z m = IntrinsicCurvature.curvature B X' Y' Z' m := by
  have hm : m ∈ (chartAt CoordinateSpace m).source := mem_chart_source CoordinateSpace m
  have htarget := (chartAt CoordinateSpace m).mapsTo hm
  have h1 := coordinateVector_curvature_eq_value B hB hSym hND X Y Z hX hY hZ m htarget
  have h2 := coordinateVector_curvature_eq_value B hB hSym hND X' Y' Z' hX' hY' hZ' m htarget
  have he : coordinateVector (IntrinsicCurvature.curvature B X Y Z) m (chartAt CoordinateSpace m m) =
      coordinateVector (IntrinsicCurvature.curvature B X' Y' Z') m (chartAt CoordinateSpace m m) := by
    rw [h1, h2, coordinateVector_eq_of_value X X' m m hm hx,
      coordinateVector_eq_of_value Y Y' m m hm hy, coordinateVector_eq_of_value Z Z' m m hm hz]
  rw [coordinateVector_at_chart _ m m hm, coordinateVector_at_chart _ m m hm] at he
  have h := congrArg (tangentFrame m m) he
  rw [tangentFrame_frameVector _ m m hm, tangentFrame_frameVector _ m m hm] at h
  exact h

end Global
end Burnett.Geometry.CurvatureJetElimination
