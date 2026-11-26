import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereFischerDecomposition
import Burnett.Analysis.CubicEnergy.AngularHarmonics.RoundSphereRotations
import Mathlib.Analysis.Calculus.ContDiff.Operations

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A06

open MvPolynomial Set Metric
open scoped ContDiff BigOperators Topology

/-- Evaluate at the actual four coordinates of the ambient Euclidean point. -/
def spherePolynomialValue (P : SpherePolynomial) (x : RotationSpace) : ℝ :=
  eval (fun i => x i) P

theorem spherePolynomialValue_contDiff (P : SpherePolynomial) :
    ContDiff ℝ ∞ (spherePolynomialValue P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have eq : spherePolynomialValue (C a) = fun _ => a :=
      funext (fun x => eval_C (f := fun i => x i) a)
    rw [eq]
    exact contDiff_const
  | add P Q hp hq =>
    have eq : spherePolynomialValue (P+Q) =
        fun x => spherePolynomialValue P x + spherePolynomialValue Q x :=
      funext (fun x => map_add (eval fun i => x i) _ _)
    rw [eq]
    exact hp.add hq
  | mul_X P i hp =>
    have hi : ContDiff ℝ ∞ (fun x : RotationSpace => x i) :=
      (EuclideanSpace.proj i : RotationSpace →L[ℝ] ℝ).contDiff
    have eq : spherePolynomialValue (P * X i) = fun x => spherePolynomialValue P x * x i := by
      funext x
      simp only [spherePolynomialValue, map_mul, eval_X]
    rw [eq]
    exact hp.mul hi

private def sphereEvaluation (x : RotationSpace) : SpherePolynomial →ₗ[ℝ] ℝ where
  toFun P := spherePolynomialValue P x
  map_add' P Q := map_add (eval fun i => x i) P Q
  map_smul' a P := by
    change eval (fun i => x i) (a • P) = a * eval (fun i => x i) P
    rw [smul_eq_C_mul, map_mul, eval_C]

/-- Evaluation of the homogeneous polynomial scales by the actual degree. -/
theorem sphereHomogeneousValue_smul (d : ℕ) (P : SphereHomogeneous d)
    (t : ℝ) (x : RotationSpace) :
    spherePolynomialValue (P : SpherePolynomial) (t • x) =
      t^d * spherePolynomialValue (P : SpherePolynomial) x := by
  let e (y : RotationSpace) := (sphereEvaluation y).comp (homogeneousSubmodule (Fin 4) ℝ d).subtype
  have equality : e (t • x) = (t^d) • e x := by
    apply (sphereHomogeneousMonomialBasis d).ext
    intro a
    change spherePolynomialValue (sphereHomogeneousMonomialBasis d a : SpherePolynomial) (t • x) =
      t^d * spherePolynomialValue (sphereHomogeneousMonomialBasis d a : SpherePolynomial) x
    rw [sphereHomogeneousMonomialBasis_apply]
    have ha : ∑ i ∈ a.val.support, a.val i = d := a.property
    simp only [spherePolynomialValue, eval_monomial, one_mul, Finsupp.prod, PiLp.smul_apply,
      smul_eq_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, ha]
  exact DFunLike.congr_fun equality P

/-- Continuous restriction to the same round unit sphere used by the rotations. -/
def spherePolynomialRestriction : SpherePolynomial →ₗ[ℝ] C(RoundSphere3, ℝ) where
  toFun P := ⟨fun x => spherePolynomialValue P x,
    (spherePolynomialValue_contDiff P).continuous.comp continuous_subtype_val⟩
  map_add' P Q := by
    ext x
    exact map_add (eval fun i => (x : RotationSpace) i) P Q
  map_smul' a P := by
    ext x
    exact (sphereEvaluation x).map_smul a P

def sphereHomogeneousRestriction (d : ℕ) : SphereHomogeneous d →ₗ[ℝ] C(RoundSphere3, ℝ) :=
  spherePolynomialRestriction.comp (homogeneousSubmodule (Fin 4) ℝ d).subtype

/-- Homogeneous radial scaling recovers each nonzero point from the unit sphere.
Continuity then gives equality at the origin. -/
theorem sphereHomogeneousRestriction_injective (d : ℕ) :
    Function.Injective (sphereHomogeneousRestriction d) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro P hP
  have offZero : EqOn (spherePolynomialValue (P : SpherePolynomial)) (fun _ => 0)
      ({(0 : RotationSpace)}ᶜ) := by
    intro x hx
    have hx0 : x ≠ 0 := hx
    let y : RoundSphere3 := ⟨‖x‖⁻¹ • x,
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm (𝕜 := ℝ) hx0)⟩
    have hy : spherePolynomialValue (P : SpherePolynomial) (y : RotationSpace) = 0 :=
      congrArg (fun f : C(RoundSphere3, ℝ) => f y) hP
    have scale : ‖x‖ • (y : RotationSpace) = x := by
      change ‖x‖ • (‖x‖⁻¹ • x) = x
      rw [smul_smul, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
    change spherePolynomialValue (P : SpherePolynomial) x = 0
    rw [← scale, sphereHomogeneousValue_smul, hy, mul_zero]
  have everywhere := (spherePolynomialValue_contDiff (P : SpherePolynomial)).continuous.ext_on
    (dense_compl_singleton (0 : RotationSpace)) continuous_const offZero
  apply Subtype.ext
  apply (show (P : SpherePolynomial).IsHomogeneous d from P.property).eq_zero_of_forall_eval_eq_zero
  intro a
  exact congrFun everywhere (WithLp.toLp 2 a : RotationSpace)

end Burnett.A06
