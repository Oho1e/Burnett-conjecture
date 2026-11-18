import Burnett.Geometry.CurvatureJetElimination
import Burnett.Geometry.SmoothTangentValueExtension
import Mathlib.Topology.Algebra.Module.Multilinear.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.CurvatureFiberTensor

open scoped BigOperators Topology
open Burnett.RicciSymbol
open ConnectionDifference CoordinateCovariantDerivative CurvatureJetElimination

theorem directionalConnection_add (Γ : CoordinateSpace → Connection) (y u v : CoordinateSpace) :
    directionalConnection Γ y (u+v) = directionalConnection Γ y u + directionalConnection Γ y v := by
  funext a b c
  exact map_add _ _ _

theorem directionalConnection_smul (Γ : CoordinateSpace → Connection) (y u : CoordinateSpace) (r : ℝ) :
    directionalConnection Γ y (r • u) = r • directionalConnection Γ y u := by
  funext a b c
  exact map_smul _ _ _

theorem connectionTerm_add_connection (Γ Δ : Connection) (u v : CoordinateSpace) :
    connectionTerm (Γ+Δ) u v = connectionTerm Γ u v + connectionTerm Δ u v := by
  ext a
  simp only [connectionTerm_apply, Pi.add_apply, PiLp.add_apply, add_mul, Finset.sum_add_distrib]

theorem connectionTerm_smul_connection (Γ : Connection) (r : ℝ) (u v : CoordinateSpace) :
    connectionTerm (r • Γ) u v = r • connectionTerm Γ u v := by
  ext a
  simp only [connectionTerm_apply, Pi.smul_apply, PiLp.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem curvatureValue_add_first (Γ : CoordinateSpace → Connection) (y u u' v w : CoordinateSpace) :
    curvatureValue (Γ y) (directionalConnection Γ y) (u+u') v w =
      curvatureValue (Γ y) (directionalConnection Γ y) u v w +
        curvatureValue (Γ y) (directionalConnection Γ y) u' v w := by
  simp only [curvatureValue, directionalConnection_add, connectionTerm_add_connection,
    connectionTerm_add_left, connectionTerm_add_right]
  abel

theorem curvatureValue_smul_first (Γ : CoordinateSpace → Connection) (y u v w : CoordinateSpace) (r : ℝ) :
    curvatureValue (Γ y) (directionalConnection Γ y) (r • u) v w =
      r • curvatureValue (Γ y) (directionalConnection Γ y) u v w := by
  simp only [curvatureValue, directionalConnection_smul, connectionTerm_smul_connection,
    connectionTerm_smul_left, connectionTerm_smul_right, smul_add, smul_sub]

theorem curvatureValue_add_second (Γ : CoordinateSpace → Connection) (y u v v' w : CoordinateSpace) :
    curvatureValue (Γ y) (directionalConnection Γ y) u (v+v') w =
      curvatureValue (Γ y) (directionalConnection Γ y) u v w +
        curvatureValue (Γ y) (directionalConnection Γ y) u v' w := by
  simp only [curvatureValue, directionalConnection_add, connectionTerm_add_connection,
    connectionTerm_add_left, connectionTerm_add_right]
  abel

theorem curvatureValue_smul_second (Γ : CoordinateSpace → Connection) (y u v w : CoordinateSpace) (r : ℝ) :
    curvatureValue (Γ y) (directionalConnection Γ y) u (r • v) w =
      r • curvatureValue (Γ y) (directionalConnection Γ y) u v w := by
  simp only [curvatureValue, directionalConnection_smul, connectionTerm_smul_connection,
    connectionTerm_smul_left, connectionTerm_smul_right, smul_add, smul_sub]

theorem curvatureValue_add_third (Γ : CoordinateSpace → Connection) (y u v w w' : CoordinateSpace) :
    curvatureValue (Γ y) (directionalConnection Γ y) u v (w+w') =
      curvatureValue (Γ y) (directionalConnection Γ y) u v w +
        curvatureValue (Γ y) (directionalConnection Γ y) u v w' := by
  simp only [curvatureValue, connectionTerm_add_right]
  abel

theorem curvatureValue_smul_third (Γ : CoordinateSpace → Connection) (y u v w : CoordinateSpace) (r : ℝ) :
    curvatureValue (Γ y) (directionalConnection Γ y) u v (r • w) =
      r • curvatureValue (Γ y) (directionalConnection Γ y) u v w := by
  simp only [curvatureValue, connectionTerm_smul_right, smul_add, smul_sub]

def curvatureLinear (Γ : CoordinateSpace → Connection) (y : CoordinateSpace) :
    CoordinateSpace →ₗ[ℝ] CoordinateSpace →ₗ[ℝ] CoordinateSpace →ₗ[ℝ] CoordinateSpace where
  toFun u :=
    { toFun := fun v =>
        { toFun := curvatureValue (Γ y) (directionalConnection Γ y) u v
          map_add' := fun w w' => curvatureValue_add_third Γ y u v w w'
          map_smul' := fun r w => curvatureValue_smul_third Γ y u v w r }
      map_add' := fun v v' => LinearMap.ext (fun w => curvatureValue_add_second Γ y u v v' w)
      map_smul' := fun r v => LinearMap.ext (fun w => curvatureValue_smul_second Γ y u v w r) }
  map_add' u u' := LinearMap.ext (fun v => LinearMap.ext (fun w => curvatureValue_add_first Γ y u u' v w))
  map_smul' r u := LinearMap.ext (fun v => LinearMap.ext (fun w => curvatureValue_smul_first Γ y u v w r))

def coordinateTensor (Γ : CoordinateSpace → Connection) (y : CoordinateSpace) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => CoordinateSpace) CoordinateSpace where
  toMultilinearMap := MultilinearMap.mk' (fun p => curvatureLinear Γ y (p 0) (p 1) (p 2))
    (by intro p i u v; fin_cases i <;> simp [Function.update, map_add])
    (by intro p i r u; fin_cases i <;> simp [Function.update, map_smul])
  cont := by
    have h : Continuous (fun p : Fin 3 → CoordinateSpace => fun a : Index =>
        curvatureValue (Γ y) (directionalConnection Γ y) (p 0) (p 1) (p 2) a) := by
      apply continuous_pi
      intro a
      simp only [curvatureValue, PiLp.add_apply, PiLp.sub_apply, connectionTerm_apply,
        directionalConnection]
      fun_prop
    exact (EuclideanSpace.equiv Index ℝ).symm.continuous.comp h

@[simp] theorem coordinateTensor_apply (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (p : Fin 3 → CoordinateSpace) :
    coordinateTensor Γ y p = curvatureValue (Γ y) (directionalConnection Γ y) (p 0) (p 1) (p 2) := rfl

end Burnett.Geometry.CurvatureFiberTensor

noncomputable section

namespace Burnett.Geometry.CurvatureFiberTensor

open Bundle Set
open scoped Manifold ContDiff Topology
open Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldMetricTransition ChartVectorField CurvatureJetElimination

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- A continuous trilinear map on the actual tangent fiber, from one preferred chart. -/
def tensorInChart (B : ManifoldBilinear.Field (M := M)) (c m : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace Model m) (TangentSpace Model m) :=
  (tangentFrame c m).compContinuousMultilinearMap
    ((coordinateTensor (BackgroundConnection.computedConnection (coordinateBilinear B c))
      (chartAt CoordinateSpace c m)).compContinuousLinearMap
        (fun _ => mfderiv Model Model (chartAt CoordinateSpace c) m))

def tensor (B : ManifoldBilinear.Field (M := M)) (m : M) :
    ContinuousMultilinearMap ℝ (fun _ : Fin 3 => TangentSpace Model m) (TangentSpace Model m) :=
  tensorInChart B m m

theorem tensorInChart_apply_fields (B : ManifoldBilinear.Field (M := M))
    (X Y Z : Field (M := M)) (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tensorInChart B c m ![X m,Y m,Z m] = tangentFrame c m
      (curvatureValue (BackgroundConnection.computedConnection (coordinateBilinear B c)
        (chartAt CoordinateSpace c m))
        (directionalConnection (BackgroundConnection.computedConnection (coordinateBilinear B c))
          (chartAt CoordinateSpace c m))
        (coordinateVector X c (chartAt CoordinateSpace c m))
        (coordinateVector Y c (chartAt CoordinateSpace c m))
        (coordinateVector Z c (chartAt CoordinateSpace c m))) := by
  change tangentFrame c m (curvatureValue _ _
    (mfderiv Model Model (chartAt CoordinateSpace c) m (X m))
    (mfderiv Model Model (chartAt CoordinateSpace c) m (Y m))
    (mfderiv Model Model (chartAt CoordinateSpace c) m (Z m))) = _
  rw [coordinateVector_at_chart X c m hm, coordinateVector_at_chart Y c m hm,
    coordinateVector_at_chart Z c m hm,
    ChartDifferential.frameVector_eq_mfderiv_chart X c m hm,
    ChartDifferential.frameVector_eq_mfderiv_chart Y c m hm,
    ChartDifferential.frameVector_eq_mfderiv_chart Z c m hm]

theorem tensorInChart_apply_fields_eq_curvature (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) :
    tensorInChart B c m ![X m,Y m,Z m] = IntrinsicCurvature.curvature B X Y Z m := by
  rw [tensorInChart_apply_fields B X Y Z c m hm]
  have hy := (chartAt CoordinateSpace c).mapsTo hm
  have h := coordinateVector_curvature_eq_value B hB hSym hND X Y Z hX hY hZ c hy
  rw [coordinateVector_at_chart _ c m hm] at h
  rw [← h, tangentFrame_frameVector _ c m hm]

theorem tensor_apply_fields_eq_curvature (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (X Y Z : Field (M := M))
    (hX : IsSmooth X) (hY : IsSmooth Y) (hZ : IsSmooth Z) (m : M) :
    tensor B m ![X m,Y m,Z m] = IntrinsicCurvature.curvature B X Y Z m :=
  tensorInChart_apply_fields_eq_curvature B hB hSym hND X Y Z hX hY hZ m m
    (mem_chart_source CoordinateSpace m)

section Hausdorff
variable [T2Space M]

theorem tensorInChart_eq (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (c d m : M)
    (hc : m ∈ (chartAt CoordinateSpace c).source) (hd : m ∈ (chartAt CoordinateSpace d).source) :
    tensorInChart B c m = tensorInChart B d m := by
  apply ContinuousMultilinearMap.ext
  intro p
  obtain ⟨X,hX,hx⟩ := SmoothTangentValueExtension.exists_isSmooth_value m (p 0)
  obtain ⟨Y,hY,hy⟩ := SmoothTangentValueExtension.exists_isSmooth_value m (p 1)
  obtain ⟨Z,hZ,hz⟩ := SmoothTangentValueExtension.exists_isSmooth_value m (p 2)
  have hp : ![X m,Y m,Z m] = p := by
    funext i
    fin_cases i <;> simp [hx,hy,hz]
  have h := (tensorInChart_apply_fields_eq_curvature B hB hSym hND X Y Z hX hY hZ c m hc).trans
    (tensorInChart_apply_fields_eq_curvature B hB hSym hND X Y Z hX hY hZ d m hd).symm
  simpa only [hp] using h

theorem tensor_eq_tensorInChart (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) : tensor B m = tensorInChart B c m :=
  tensorInChart_eq B hB hSym hND m c m (mem_chart_source CoordinateSpace m) hm

end Hausdorff
end Burnett.Geometry.CurvatureFiberTensor
