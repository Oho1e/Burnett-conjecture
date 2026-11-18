import Burnett.Geometry.CurvatureFiberTensor
import Burnett.Geometry.CurvatureComponents
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.IntrinsicRicciTrace

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol
open ConnectionDifference CurvatureDifference CurvatureJetElimination CurvatureFiberTensor
open ManifoldMetric ManifoldMetricTransition ChartVectorField

theorem coordinateTensor_basis (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hΓ : DifferentiableConnectionAt Γ y) (a b c d : Index) :
    coordinateTensor Γ y ![EuclideanSpace.single c 1,EuclideanSpace.single d 1,EuclideanSpace.single b 1] a =
      CurvatureComponents.components (Γ y) (coordinateConnectionJet Γ y) a b c d := by
  have h := coordinateCurvature_eq_curvatureValue Γ
    (fun _ => EuclideanSpace.single c 1) (fun _ => EuclideanSpace.single d 1)
    (fun _ => EuclideanSpace.single b 1) y hΓ (by fun_prop) (by fun_prop) (by fun_prop)
  have hc := congrArg (fun z : CoordinateSpace => z a) h
  dsimp only at hc
  rw [CurvatureComponents.coordinateCurvature_basis Γ y hΓ a b c d] at hc
  simpa only [coordinateTensor_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] using hc.symm

theorem coordinateRicci_eq_coordinateTensor_trace (Γ : CoordinateSpace → Connection) (y : CoordinateSpace)
    (hΓ : DifferentiableConnectionAt Γ y)
    (hSym : ∀ᶠ z in 𝓝 y, ∀ a b d, Γ z a b d = Γ z a d b) (b d : Index) :
    coordinateRicci Γ y b d = ∑ a : Index,
      coordinateTensor Γ y ![EuclideanSpace.single a 1,EuclideanSpace.single d 1,EuclideanSpace.single b 1] a := by
  rw [CurvatureComponents.coordinateRicci_eq_trace_components Γ y hSym b d]
  apply Finset.sum_congr rfl
  intro a _
  exact (coordinateTensor_basis Γ y hΓ a b a d).symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

theorem forward_tangentFrame (c m : M) (hm : m ∈ (chartAt CoordinateSpace c).source)
    (v : CoordinateSpace) :
    mfderiv Model Model (chartAt CoordinateSpace c) m (tangentFrame c m v) = v := by
  let e := trivializationAt CoordinateSpace (TangentSpace Model) c
  have he : e.continuousLinearMapAt ℝ m = mfderiv Model Model (chartAt CoordinateSpace c) m := by
    simpa only [Model, mfld_simps] using
      TangentBundle.continuousLinearMapAt_trivializationAt (I := Model) hm
  rw [← he]
  change e.continuousLinearMapAt ℝ m (e.symmL ℝ m v) = v
  exact e.continuousLinearMapAt_symmL (R := ℝ) hm v

end Burnett.Geometry.IntrinsicRicciTrace

noncomputable section

namespace Burnett.Geometry.IntrinsicRicciTrace

open Bundle Set Filter
open scoped Manifold ContDiff Topology BigOperators
open Burnett.RicciSymbol
open ConnectionDifference CurvatureDifference CurvatureJetElimination CurvatureFiberTensor
open ManifoldMetric ManifoldMetricTransition ChartVectorField

def coordinateEnd (Γ : CoordinateSpace → Connection) (y u v : CoordinateSpace) :
    CoordinateSpace →ₗ[ℝ] CoordinateSpace :=
  (coordinateTensor Γ y).toMultilinearMap.toLinearMap ![0,v,u] 0

@[simp] theorem coordinateEnd_apply (Γ : CoordinateSpace → Connection) (y u v x : CoordinateSpace) :
    coordinateEnd Γ y u v x = coordinateTensor Γ y ![x,v,u] := by
  change coordinateTensor Γ y (Function.update ![0,v,u] 0 x) = coordinateTensor Γ y ![x,v,u]
  congr 1
  funext i
  fin_cases i <;> simp

theorem trace_coordinateEnd_eq_sum (Γ : CoordinateSpace → Connection) (y u v : CoordinateSpace) :
    LinearMap.trace ℝ CoordinateSpace (coordinateEnd Γ y u v) =
      ∑ a : Index, coordinateTensor Γ y ![EuclideanSpace.single a 1,v,u] a := by
  rw [LinearMap.trace_eq_matrix_trace ℝ coordinateBasis]
  simp [Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, coordinateBasis,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- The actual fiber endomorphism X ↦ R(X,V)U, with X the traced slot. -/
def curvatureEnd (B : ManifoldBilinear.Field (M := M)) (m : M) (U V : TangentSpace Model m) :
    TangentSpace Model m →ₗ[ℝ] TangentSpace Model m :=
  (tensor B m).toMultilinearMap.toLinearMap ![0,V,U] 0

@[simp] theorem curvatureEnd_apply (B : ManifoldBilinear.Field (M := M))
    (m : M) (U V X : TangentSpace Model m) :
    curvatureEnd B m U V X = tensor B m ![X,V,U] := by
  change tensor B m (Function.update ![0,V,U] 0 X) = tensor B m ![X,V,U]
  congr 1
  funext i
  fin_cases i <;> simp

/-- Ricci is the genuine linear-algebra trace of the true curvature endomorphism.
    No coordinate Ricci array or coordinate-vacuum hypothesis occurs here. -/
def ricci (B : ManifoldBilinear.Field (M := M)) (m : M) (U V : TangentSpace Model m) : ℝ :=
  LinearMap.trace ℝ (TangentSpace Model m) (curvatureEnd B m U V)

theorem tensorInChart_apply (B : ManifoldBilinear.Field (M := M)) (c m : M)
    (X Y Z : TangentSpace Model m) :
    tensorInChart B c m ![X,Y,Z] = tangentFrame c m
      (coordinateTensor (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (chartAt CoordinateSpace c m) ![
          mfderiv Model Model (chartAt CoordinateSpace c) m X,
          mfderiv Model Model (chartAt CoordinateSpace c) m Y,
          mfderiv Model Model (chartAt CoordinateSpace c) m Z]) := by
  simp only [tensorInChart, ContinuousLinearMap.compContinuousMultilinearMap_coe,
    Function.comp_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply]
  apply congrArg (tangentFrame c m)
  apply congrArg (coordinateTensor _ _)
  funext i
  fin_cases i <;> rfl

section Hausdorff
variable [T2Space M]

theorem curvatureEnd_eq_chart_composition (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) (U V : TangentSpace Model m) :
    curvatureEnd B m U V =
      ((tangentFrame c m).toLinearMap.comp
        (coordinateEnd (BackgroundConnection.computedConnection (coordinateBilinear B c))
          (chartAt CoordinateSpace c m)
          (mfderiv Model Model (chartAt CoordinateSpace c) m U)
          (mfderiv Model Model (chartAt CoordinateSpace c) m V))).comp
        (mfderiv Model Model (chartAt CoordinateSpace c) m).toLinearMap := by
  apply LinearMap.ext
  intro X
  rw [curvatureEnd_apply, tensor_eq_tensorInChart B hB hSym hND c m hm, tensorInChart_apply]
  simp only [LinearMap.comp_apply, ContinuousLinearMap.coe_coe, coordinateEnd_apply]
  rfl

theorem ricci_eq_coordinate_trace (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) (U V : TangentSpace Model m) :
    ricci B m U V = LinearMap.trace ℝ CoordinateSpace
      (coordinateEnd (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (chartAt CoordinateSpace c m)
        (mfderiv Model Model (chartAt CoordinateSpace c) m U)
        (mfderiv Model Model (chartAt CoordinateSpace c) m V)) := by
  let A : TangentSpace Model m →ₗ[ℝ] CoordinateSpace :=
    (mfderiv Model Model (chartAt CoordinateSpace c) m).toLinearMap
  let I := (tangentFrame c m).toLinearMap
  let C := coordinateEnd (BackgroundConnection.computedConnection (coordinateBilinear B c))
    (chartAt CoordinateSpace c m)
    (mfderiv Model Model (chartAt CoordinateSpace c) m U)
    (mfderiv Model Model (chartAt CoordinateSpace c) m V)
  let e := (trivializationAt CoordinateSpace (TangentSpace Model) m).linearEquivAt ℝ m
    (mem_chart_source CoordinateSpace m)
  haveI : FiniteDimensional ℝ (TangentSpace Model m) := e.symm.finiteDimensional
  have hAI : A.comp I = LinearMap.id :=
    LinearMap.ext (fun x => forward_tangentFrame c m hm x)
  unfold ricci
  rw [curvatureEnd_eq_chart_composition B hB hSym hND c m hm U V]
  change LinearMap.trace ℝ (TangentSpace Model m) ((I.comp C).comp A) =
    LinearMap.trace ℝ CoordinateSpace C
  rw [LinearMap.trace_comp_comm' A (I.comp C), ← LinearMap.comp_assoc, hAI, LinearMap.id_comp]

theorem ricci_coordinate_basis (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (c m : M)
    (hm : m ∈ (chartAt CoordinateSpace c).source) (b d : Index) :
    ricci B m (tangentFrame c m (EuclideanSpace.single b 1))
      (tangentFrame c m (EuclideanSpace.single d 1)) =
      coordinateRicci (BackgroundConnection.computedConnection (coordinateBilinear B c))
        (chartAt CoordinateSpace c m) b d := by
  rw [ricci_eq_coordinate_trace B hB hSym hND c m hm,
    forward_tangentFrame c m hm, forward_tangentFrame c m hm, trace_coordinateEnd_eq_sum]
  apply (coordinateRicci_eq_coordinateTensor_trace _ _ ?_ ?_ b d).symm
  · have hΓ := SmoothMetricConnection.contDiffOn_coordinateBilinear_connection B hB hND c
    intro a b d
    exact ((contDiffOn_pi.mp (contDiffOn_pi.mp (contDiffOn_pi.mp hΓ a) b) d).contDiffAt
      ((chartAt CoordinateSpace c).open_target.mem_nhds ((chartAt CoordinateSpace c).mapsTo hm))).differentiableAt
        (by simp)
  · apply Eventually.of_forall
    intro z a b d
    exact christoffel_torsion_free _ _ (coordinateJet_symmetric _ z
      (Eventually.of_forall (fun w => FiberMetric.covariant_symmetric _
        (ManifoldBilinear.coordinateBilinear_symmetric B hSym c w) coordinateBasis))) a b d

def IsVacuum (B : ManifoldBilinear.Field (M := M)) : Prop :=
  ∀ (m : M) (U V : TangentSpace Model m), ricci B m U V = 0

theorem coordinateVacuum_of_intrinsic (B : ManifoldBilinear.Field (M := M))
    (hB : ManifoldBilinear.IsSmooth B) (hSym : ManifoldBilinear.IsSymmetric B)
    (hND : ManifoldBilinear.IsNondegenerate B) (hVac : IsVacuum B) (c : M)
    (y : CoordinateSpace) (hy : y ∈ (chartAt CoordinateSpace c).target) (b d : Index) :
    coordinateRicci (BackgroundConnection.computedConnection (coordinateBilinear B c)) y b d = 0 := by
  let m := (chartAt CoordinateSpace c).symm y
  have hm : m ∈ (chartAt CoordinateSpace c).source := (chartAt CoordinateSpace c).symm_mapsTo hy
  have h := hVac m (tangentFrame c m (EuclideanSpace.single b 1))
    (tangentFrame c m (EuclideanSpace.single d 1))
  rw [ricci_coordinate_basis B hB hSym hND c m hm b d] at h
  simpa only [m, (chartAt CoordinateSpace c).right_inv hy] using h

theorem sequence_coordinateVacuum_of_intrinsic (g : ℕ → ManifoldBilinear.Field (M := M))
    (hg : ∀ n, ManifoldBilinear.IsSmooth (g n)) (hs : ∀ n, ManifoldBilinear.IsSymmetric (g n))
    (hn : ∀ n, ManifoldBilinear.IsNondegenerate (g n)) (hv : ∀ n, IsVacuum (g n)) (c : M) :
    ∀ n y, y ∈ (chartAt CoordinateSpace c).target → ∀ b d,
      coordinateRicci (BackgroundConnection.computedConnection (coordinateBilinear (g n) c)) y b d = 0 :=
  fun n y hy b d => coordinateVacuum_of_intrinsic (g n) (hg n) (hs n) (hn n) (hv n) c y hy b d

end Hausdorff
end Burnett.Geometry.IntrinsicRicciTrace
