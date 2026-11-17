import Burnett.Geometry.AuxiliaryConnection
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Analysis.Calculus.VectorField

/-!
# Covariant differentiation of actual coordinate vector fields

The derivative acts on genuine vector fields by their Frechet derivatives
and a computed Christoffel correction. The dual covariant-two operation is
defined from actual scalar pairings. Connection laws, torsion and its
coordinate-frame components are proved here. Chart naturality and a global
Levi-Civita connection are separate obligations.
-/

noncomputable section
namespace Burnett.Geometry.CoordinateCovariantDerivative
open scoped BigOperators Topology
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.BackgroundConnection

abbrev VectorField := CoordinateSpace → CoordinateSpace

/-- The actual bilinear Christoffel correction on coordinate vectors. -/
def connectionTerm (Γ : Connection) (v w : CoordinateSpace) : CoordinateSpace :=
  WithLp.toLp 2 (fun a => ∑ b, ∑ c, Γ a b c * v b * w c)

@[simp] theorem connectionTerm_apply (Γ : Connection) (v w : CoordinateSpace) (a : Index) :
    connectionTerm Γ v w a = ∑ b, ∑ c, Γ a b c * v b * w c := rfl

theorem connectionTerm_add_left (Γ : Connection) (u v w : CoordinateSpace) :
    connectionTerm Γ (u + v) w = connectionTerm Γ u w + connectionTerm Γ v w := by
  ext a
  simp [connectionTerm, mul_add, add_mul, Finset.sum_add_distrib]

theorem connectionTerm_add_right (Γ : Connection) (u v w : CoordinateSpace) :
    connectionTerm Γ u (v + w) = connectionTerm Γ u v + connectionTerm Γ u w := by
  ext a
  simp [connectionTerm, mul_add, Finset.sum_add_distrib]

theorem connectionTerm_smul_left (Γ : Connection) (r : ℝ) (v w : CoordinateSpace) :
    connectionTerm Γ (r • v) w = r • connectionTerm Γ v w := by
  ext a
  simp only [connectionTerm_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [show ∀ b c, Γ a b c * (r * v b) * w c = r * (Γ a b c * v b * w c) by intros; ring]
  simp [Finset.mul_sum]

theorem connectionTerm_smul_right (Γ : Connection) (r : ℝ) (v w : CoordinateSpace) :
    connectionTerm Γ v (r • w) = r • connectionTerm Γ v w := by
  ext a
  simp only [connectionTerm_apply, PiLp.smul_apply, smul_eq_mul]
  simp_rw [show ∀ b c, Γ a b c * v b * (r * w c) = r * (Γ a b c * v b * w c) by intros; ring]
  simp [Finset.mul_sum]

/-- Coordinate covariant differentiation of a genuine vector field.
Only the germ of W at x and values V x, Γ x are used. -/
def derivative (Γ : CoordinateSpace → Connection) (V W : VectorField)
    (x : CoordinateSpace) : CoordinateSpace :=
  fderiv ℝ W x (V x) + connectionTerm (Γ x) (V x) (W x)

theorem derivative_add_left (Γ : CoordinateSpace → Connection) (U V W : VectorField)
    (x : CoordinateSpace) :
    derivative Γ (U + V) W x = derivative Γ U W x + derivative Γ V W x := by
  simp [derivative, connectionTerm_add_left, map_add, add_add_add_comm]

theorem derivative_smul_left (Γ : CoordinateSpace → Connection) (f : CoordinateSpace → ℝ)
    (V W : VectorField) (x : CoordinateSpace) :
    derivative Γ (f • V) W x = f x • derivative Γ V W x := by
  simp [derivative, connectionTerm_smul_left, map_smul, smul_add]

theorem derivative_add_right (Γ : CoordinateSpace → Connection) (U V W : VectorField)
    (x : CoordinateSpace) (hV : DifferentiableAt ℝ V x) (hW : DifferentiableAt ℝ W x) :
    derivative Γ U (V + W) x = derivative Γ U V x + derivative Γ U W x := by
  simp [derivative, fderiv_add hV hW, connectionTerm_add_right, add_add_add_comm]

theorem derivative_smul_right (Γ : CoordinateSpace → Connection) (f : CoordinateSpace → ℝ)
    (V W : VectorField) (x : CoordinateSpace)
    (hf : DifferentiableAt ℝ f x) (hW : DifferentiableAt ℝ W x) :
    derivative Γ V (f • W) x =
      f x • derivative Γ V W x + (fderiv ℝ f x (V x)) • W x := by
  simp [derivative, fderiv_smul hf hW, connectionTerm_smul_right,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply, smul_add]
  abel

theorem connectionTerm_symm (Γ : Connection)
    (hΓ : ∀ a b c, Γ a b c = Γ a c b) (v w : CoordinateSpace) :
    connectionTerm Γ v w = connectionTerm Γ w v := by
  ext a
  simp only [connectionTerm_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro c hc
  rw [hΓ a c b]
  ring

@[simp] theorem connectionTerm_basis (Γ : Connection) (b c a : Index) :
    connectionTerm Γ (EuclideanSpace.single b 1) (EuclideanSpace.single c 1) a =
      Γ a b c := by
  simp [connectionTerm, EuclideanSpace.single_apply]

/-- The genuine bilinear form represented by a coordinate tensor. -/
def tensorForm (H : Tensor2) : LinearMap.BilinForm ℝ CoordinateSpace :=
  Matrix.toBilin coordinateBasis H

@[simp] theorem tensorForm_apply (H : Tensor2) (v w : CoordinateSpace) :
    tensorForm H v w = ∑ a, ∑ b, v a * H a b * w b := by
  simp [tensorForm, Matrix.toBilin_apply, coordinateBasis, EuclideanSpace.basisFun_repr]

/-- Dual differentiation is defined by differentiating the actual scalar
pairing and subtracting the two vector-slot derivatives. -/
def inducedCov2 (Γ : CoordinateSpace → Connection) (H : CoordinateSpace → Tensor2)
    (V U W : VectorField) (x : CoordinateSpace) : ℝ :=
  fderiv ℝ (fun y => tensorForm (H y) (U y) (W y)) x (V x) -
    tensorForm (H x) (derivative Γ V U x) (W x) -
    tensorForm (H x) (U x) (derivative Γ V W x)

/-- Its actual coordinate-frame components are the already defined jet. -/
theorem inducedCov2_basis (Γ : CoordinateSpace → Connection)
    (H : CoordinateSpace → Tensor2) (x : CoordinateSpace) (b c d : Index) :
    inducedCov2 Γ H (fun _ => EuclideanSpace.single b 1)
      (fun _ => EuclideanSpace.single c 1) (fun _ => EuclideanSpace.single d 1) x =
      covariantJet (Γ x) (H x) (coordinateJet H x) b c d := by
  simp [inducedCov2, tensorForm_apply, derivative, coordinateJet, covariantJet,
    EuclideanSpace.single_apply, mul_comm]

/-- The same metric perturbation and fixed auxiliary Christoffel field are
used on both sides; this is an actual dual-derivative component identity. -/
theorem inducedCov2_auxiliaryPerturbationJet
    (r g₀ g₁ : CoordinateSpace → LinearMap.BilinForm ℝ CoordinateSpace)
    (x : CoordinateSpace) (b c d : Index) :
    inducedCov2 (computedConnection r)
      (fun y => metricComponents g₁ y - metricComponents g₀ y)
      (fun _ => EuclideanSpace.single b 1) (fun _ => EuclideanSpace.single c 1)
      (fun _ => EuclideanSpace.single d 1) x =
      AuxiliaryConnection.auxiliaryPerturbationJet r g₀ g₁ x b c d :=
  inducedCov2_basis _ _ x b c d

/-- The torsion is computed against mathlib's actual Lie bracket. -/
theorem derivative_torsion_free (Γ : CoordinateSpace → Connection)
    (V W : VectorField) (x : CoordinateSpace)
    (hΓ : ∀ a b c, Γ x a b c = Γ x a c b) :
    derivative Γ V W x - derivative Γ W V x = _root_.VectorField.lieBracket ℝ V W x := by
  rw [derivative, derivative, connectionTerm_symm (Γ x) hΓ]
  exact add_sub_add_right_eq_sub _ _ _

end Burnett.Geometry.CoordinateCovariantDerivative
