import Burnett.Geometry.Cotangent.Core
import Burnett.Geometry.IntrinsicRicciTrace
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Contravariant tensor tests, intrinsic Ricci contraction, and coordinate components. -/

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.ContravariantTensor

open Bundle Set Matrix Module Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricTransition
open Burnett.Geometry.CurvatureDifference (coordinateRicci)
open BackgroundConnection IntrinsicRicciTrace UnitNullCompactness
open scoped BigOperators ContDiff Manifold

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Contract a bilinear form on the dual with a bilinear form on the underlying space. -/
def dualBilinearContraction [FiniteDimensional ℝ V]
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (R : LinearMap.BilinForm ℝ V) : ℝ :=
  LinearMap.trace ℝ V
    ((Module.evalEquiv ℝ V).symm.toLinearMap.comp ((LinearMap.flip Q).comp R))

theorem dualBilinearContraction_eq_sum [FiniteDimensional ℝ V]
    (b : Basis Index ℝ V) (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ V)) (R : LinearMap.BilinForm ℝ V) :
    dualBilinearContraction Q R = ∑ i, ∑ j, Q (b.dualBasis i) (b.dualBasis j) * R (b i) (b j) := by
  classical
  rw [dualBilinearContraction, LinearMap.trace_eq_matrix_trace ℝ b]
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, ← Basis.dualBasis_apply,
    LinearMap.comp_apply, LinearEquiv.coe_coe, Module.apply_evalEquiv_symm_apply,
    LinearMap.comp_apply, LinearMap.flip_apply]
  have h := congrArg (Q (b.dualBasis i)) (b.dualBasis.sum_repr (R (b i)))
  simpa only [map_sum, map_smul, smul_eq_mul, Basis.dualBasis_repr, mul_comm] using h.symm

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
  [IsManifold Model ∞ M]

/-- A contravariant two-tensor evaluates on the two algebraic covectors of each actual fiber. -/
abbrev ContravariantTwoTensor (M : Type*) [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
    [IsManifold Model ∞ M] :=
  (x : M) → LinearMap.BilinForm ℝ (Module.Dual ℝ (TangentSpace Model x))

/-- The coordinate basis carried to the actual tangent fiber by the preferred chart. -/
def tensorTangentBasis (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) :
    Basis Index ℝ (TangentSpace Model x) :=
  coordinateBasis.map
    ((trivializationAt CoordinateSpace (TangentSpace Model) c).continuousLinearEquivAt ℝ x hx).symm.toLinearEquiv

theorem tensorTangentBasis_apply (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) (i : Index) :
    tensorTangentBasis c x hx i = tangentFrame c x (coordinateBasis i) := by
  rw [tensorTangentBasis, Basis.map_apply]
  rfl

/-- The actual coframe element whose coordinate components are the (i)-th unit vector. -/
def coordinateCovectorBasis (c x : M) (i : Index) : Module.Dual ℝ (TangentSpace Model x) :=
  (cotangentAssemble c (x, fun j => if j = i then 1 else 0)).2.toLinearMap

theorem coordinateCovectorBasis_eq_dualBasis
    (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) (i : Index) :
    coordinateCovectorBasis c x i = (tensorTangentBasis c x hx).dualBasis i := by
  apply (tensorTangentBasis c x hx).ext
  intro j
  rw [Basis.dualBasis_apply_self, tensorTangentBasis_apply]
  have h := congrFun (cotangentCoords_assemble c (x, fun j => if j = i then 1 else 0) hx) j
  simpa only [cotangentCoords, cotangentTrivialization_apply, coordinateCovectorBasis,
    ContinuousLinearMap.coe_coe] using h

/-- Components of a contravariant tensor in the actual coordinate coframe. -/
def contravariantComponents (Q : ContravariantTwoTensor M) (c : M) (y : CoordinateSpace)
    (i j : Index) : ℝ :=
  let x := (chartAt CoordinateSpace c).symm y
  Q x (coordinateCovectorBasis c x i) (coordinateCovectorBasis c x j)

theorem contravariantComponents_chart (Q : ContravariantTwoTensor M) (c x : M)
    (hx : x ∈ (chartAt CoordinateSpace c).source) (i j : Index) :
    contravariantComponents Q c (chartAt CoordinateSpace c x) i j =
      Q x ((tensorTangentBasis c x hx).dualBasis i) ((tensorTangentBasis c x hx).dualBasis j) := by
  unfold contravariantComponents
  rw [(chartAt CoordinateSpace c).left_inv hx]
  simp only [coordinateCovectorBasis_eq_dualBasis c x hx]

/-- Smoothness in each preferred chart on its target. -/
def IsSmoothContravariant (Q : ContravariantTwoTensor M) : Prop :=
  ∀ c i j, ContDiffOn ℝ ∞ (fun y => contravariantComponents Q c y i j) (chartAt CoordinateSpace c).target

def HasCompactSupportContravariant (Q : ContravariantTwoTensor M) : Prop :=
  IsCompact (closure {x | Q x ≠ 0})

/-- The compactly supported smooth symmetric tests of the Einstein moment identity. -/
def IsTensorTest (Q : ContravariantTwoTensor M) : Prop :=
  (∀ x, (Q x).IsSymm) ∧ HasCompactSupportContravariant Q ∧ IsSmoothContravariant Q

private def curvatureEndInFirstSlot (B : Field (M := M)) (x : M) (v z : TangentSpace Model x) :=
  (CurvatureFiberTensor.tensor B x).toMultilinearMap.toLinearMap ![z,v,0] (2 : Fin 3)

private theorem curvatureEndInFirstSlot_apply (B : Field (M := M)) (x : M) (u v z : TangentSpace Model x) :
    curvatureEndInFirstSlot B x v z u = curvatureEnd B x u v z := by
  rw [curvatureEnd_apply]
  change CurvatureFiberTensor.tensor B x (Function.update ![z,v,0] (2 : Fin 3) u) = _
  congr 1
  funext k
  fin_cases k <;> simp

private def curvatureEndInSecondSlot (B : Field (M := M)) (x : M) (u z : TangentSpace Model x) :=
  (CurvatureFiberTensor.tensor B x).toMultilinearMap.toLinearMap ![z,0,u] (1 : Fin 3)

private theorem curvatureEndInSecondSlot_apply (B : Field (M := M)) (x : M) (u v z : TangentSpace Model x) :
    curvatureEndInSecondSlot B x u z v = curvatureEnd B x u v z := by
  rw [curvatureEnd_apply]
  change CurvatureFiberTensor.tensor B x (Function.update ![z,0,u] (1 : Fin 3) v) = _
  congr 1
  funext k
  fin_cases k <;> simp

/-- The intrinsic Ricci trace as a bilinear form on the actual tangent space. -/
def ricciBilinearForm (B : Field (M := M)) (x : M) : LinearMap.BilinForm ℝ (TangentSpace Model x) :=
  LinearMap.mk₂ ℝ (ricci B x)
    (fun u u' v => by
      have h : curvatureEnd B x (u + u') v = curvatureEnd B x u v + curvatureEnd B x u' v := by
        ext z
        simpa only [curvatureEndInFirstSlot_apply, LinearMap.add_apply] using
          (curvatureEndInFirstSlot B x v z).map_add u u'
      simp [ricci, h])
    (fun a u v => by
      have h : curvatureEnd B x (a • u) v = a • curvatureEnd B x u v := by
        ext z
        simpa only [curvatureEndInFirstSlot_apply, LinearMap.smul_apply] using
          (curvatureEndInFirstSlot B x v z).map_smul a u
      simp [ricci, h])
    (fun u v v' => by
      have h : curvatureEnd B x u (v + v') = curvatureEnd B x u v + curvatureEnd B x u v' := by
        ext z
        simpa only [curvatureEndInSecondSlot_apply, LinearMap.add_apply] using
          (curvatureEndInSecondSlot B x u z).map_add v v'
      simp [ricci, h])
    (fun a u v => by
      have h : curvatureEnd B x u (a • v) = a • curvatureEnd B x u v := by
        ext z
        simpa only [curvatureEndInSecondSlot_apply, LinearMap.smul_apply] using
          (curvatureEndInSecondSlot B x u z).map_smul a v
      simp [ricci, h])

theorem ricciBilinearForm_apply (B : Field (M := M)) (x : M) (u v : TangentSpace Model x) :
    ricciBilinearForm B x u v = ricci B x u v := rfl

def contractAt (x : M) (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ (TangentSpace Model x)))
    (R : LinearMap.BilinForm ℝ (TangentSpace Model x)) : ℝ := by
  letI : FiniteDimensional ℝ (TangentSpace Model x) :=
    Module.Finite.of_basis (tensorTangentBasis x x (mem_chart_source CoordinateSpace x))
  exact dualBilinearContraction Q R

theorem contractAt_eq_sum (x : M) (b : Basis Index ℝ (TangentSpace Model x))
    (Q : LinearMap.BilinForm ℝ (Module.Dual ℝ (TangentSpace Model x)))
    (R : LinearMap.BilinForm ℝ (TangentSpace Model x)) :
    contractAt x Q R = ∑ i, ∑ j, Q (b.dualBasis i) (b.dualBasis j) * R (b i) (b j) := by
  letI : FiniteDimensional ℝ (TangentSpace Model x) := Module.Finite.of_basis b
  unfold contractAt
  exact dualBilinearContraction_eq_sum b Q R

/-- Pair the test with the intrinsic Ricci tensor at a base point. -/
def intrinsicTensorBase (B : Field (M := M)) (Q : ContravariantTwoTensor M) (x : M) : ℝ :=
  contractAt x (Q x) (ricciBilinearForm B x)

/-- Evaluate the test twice on the covector of the actual cotangent bundle. -/
def intrinsicTensorPhase (Q : ContravariantTwoTensor M) (p : CotangentBundle M) : ℝ :=
  Q p.proj p.2.toLinearMap p.2.toLinearMap

theorem intrinsicTensorBase_eq_components [T2Space M]
    (B : Field (M := M)) (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (Q : ContravariantTwoTensor M) (c x : M) (hx : x ∈ (chartAt CoordinateSpace c).source) :
    intrinsicTensorBase B Q x = ∑ i, ∑ j,
      contravariantComponents Q c (chartAt CoordinateSpace c x) i j *
        coordinateRicci (computedConnection (coordinateBilinear B c)) (chartAt CoordinateSpace c x) i j := by
  let b := tensorTangentBasis c x hx
  rw [intrinsicTensorBase, contractAt_eq_sum x b]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [contravariantComponents_chart Q c x hx]
  change Q x (b.dualBasis i) (b.dualBasis j) * ricci B x (b i) (b j) = _
  rw [tensorTangentBasis_apply, tensorTangentBasis_apply,
    show coordinateBasis i = EuclideanSpace.single i 1 from EuclideanSpace.basisFun_apply _ _ i,
    show coordinateBasis j = EuclideanSpace.single j 1 from EuclideanSpace.basisFun_apply _ _ j,
    ricci_coordinate_basis B hB hs hn c x hx]

theorem intrinsicTensorPhase_eq_components
    (Q : ContravariantTwoTensor M) (c : M) (p : CotangentBundle M)
    (hp : p.proj ∈ (chartAt CoordinateSpace c).source) :
    intrinsicTensorPhase Q p = ∑ i, ∑ j,
      contravariantComponents Q c (chartAt CoordinateSpace c p.proj) i j *
        (cotangentCoords c p i * cotangentCoords c p j) := by
  let b := tensorTangentBasis c p.proj hp
  let v : Module.Dual ℝ (TangentSpace Model p.proj) := p.2.toLinearMap
  have hv : v = ∑ i, cotangentCoords c p i • b.dualBasis i := by
    symm
    have h (i : Index) : b.dualBasis.repr v i = cotangentCoords c p i := by
      rw [Basis.dualBasis_repr, tensorTangentBasis_apply, cotangentCoords, cotangentTrivialization_apply]
      rfl
    simpa only [h] using b.dualBasis.sum_repr v
  have hc (i j : Index) : contravariantComponents Q c (chartAt CoordinateSpace c p.proj) i j =
      Q p.proj (b.dualBasis i) (b.dualBasis j) :=
    contravariantComponents_chart Q c p.proj hp i j
  change Q p.proj v v = _
  calc
    _ = Q p.proj (∑ i, cotangentCoords c p i • b.dualBasis i) v :=
      congrArg (fun z => Q p.proj z v) hv
    _ = ∑ i, cotangentCoords c p i * Q p.proj (b.dualBasis i) v := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hv]
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, hc]
      apply Finset.sum_congr rfl
      intro j _
      ring

end Burnett.Geometry.ContravariantTensor
