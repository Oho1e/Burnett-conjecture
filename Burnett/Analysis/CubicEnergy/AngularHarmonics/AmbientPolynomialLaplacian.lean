import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicL2
import Burnett.Analysis.CubicEnergy.AngularHarmonics.RoundSphereCasimir

set_option autoImplicit false
set_option maxHeartbeats 6500000

noncomputable section

namespace Burnett.A06

open MvPolynomial MeasureTheory
open scoped BigOperators ContDiff

private theorem spherePolynomialValue_add (P Q : SpherePolynomial) :
    spherePolynomialValue (P + Q) = spherePolynomialValue P + spherePolynomialValue Q :=
  funext fun x => map_add (eval fun i => x i) P Q

private theorem spherePolynomialValue_mul_X (P : SpherePolynomial) (j : Fin 4) :
    spherePolynomialValue (P * X j) =
      spherePolynomialValue P * (EuclideanSpace.proj j : RotationSpace →L[ℝ] ℝ) := by
  funext x
  simp [spherePolynomialValue, Pi.mul_apply]

/-- The real directional derivative in a unit coordinate direction evaluates
the formal derivative of the original four-variable polynomial. -/
theorem spherePolynomialValue_fderiv_coordinate (P : SpherePolynomial)
    (x : RotationSpace) (i : Fin 4) :
    fderiv ℝ (spherePolynomialValue P) x (EuclideanSpace.single i 1) =
      spherePolynomialValue (pderiv i P) x := by
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h : spherePolynomialValue (C a) = Function.const RotationSpace a :=
      funext fun y => eval_C (f := fun j => y j) a
    rw [h, fderiv_const, pderiv_C]
    simp [spherePolynomialValue]
  | add P Q hP hQ =>
    rw [spherePolynomialValue_add, fderiv_add
      ((contDiff_infty.mp (spherePolynomialValue_contDiff P) 1).differentiable_one x)
      ((contDiff_infty.mp (spherePolynomialValue_contDiff Q) 1).differentiable_one x), map_add]
    simp only [ContinuousLinearMap.add_apply, hP, hQ, spherePolynomialValue_add, Pi.add_apply]
  | mul_X P j hP =>
    rw [spherePolynomialValue_mul_X, fderiv_mul
      ((contDiff_infty.mp (spherePolynomialValue_contDiff P) 1).differentiable_one x)
      (EuclideanSpace.proj j : RotationSpace →L[ℝ] ℝ).differentiableAt,
      ContinuousLinearMap.fderiv, pderiv_mul, spherePolynomialValue_add, Pi.add_apply]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, hP]
    by_cases h : j = i
    · subst j
      simp [spherePolynomialValue]
      ring
    · simp [spherePolynomialValue, h, mul_comm]

/-- The genuine ambient Euclidean Laplacian agrees with evaluating the sum of
formal second partial derivatives in the four-variable polynomial ring. -/
theorem spherePolynomialValue_laplacian (P : SpherePolynomial) (x : RotationSpace) :
    InnerProductSpace.laplacian (spherePolynomialValue P) x =
      spherePolynomialValue (polynomialLaplacian P) x := by
  rw [InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis _ (EuclideanSpace.basisFun (Fin 4) ℝ),
    polynomialLaplacian_apply]
  change (∑ i : Fin 4, iteratedFDeriv ℝ 2 (spherePolynomialValue P) x
    ![EuclideanSpace.basisFun (Fin 4) ℝ i, EuclideanSpace.basisFun (Fin 4) ℝ i]) =
    (eval fun i => x i) (∑ i : Fin 4, pderiv i (pderiv i P))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    EuclideanSpace.basisFun_apply]
  let v : RotationSpace := EuclideanSpace.single i 1
  have hd : Differentiable ℝ (fderiv ℝ (spherePolynomialValue P)) :=
    ((contDiff_infty.mp (spherePolynomialValue_contDiff P) 2).fderiv_right (m := 1) (by norm_num)).differentiable_one
  have hfun : spherePolynomialValue (pderiv i P) =
      fun y => fderiv ℝ (spherePolynomialValue P) y v :=
    funext fun y => (spherePolynomialValue_fderiv_coordinate P y i).symm
  have h := spherePolynomialValue_fderiv_coordinate (pderiv i P) x i
  rw [hfun, fderiv_clm_apply (hd x) (differentiableAt_const v)] at h
  simpa only [fderiv_fun_const, Pi.zero_apply, ContinuousLinearMap.comp_zero,
    zero_add, ContinuousLinearMap.flip_apply, v] using h

/-- The continuous representatives of the same real \(L²\) basis have
eigenvalue \(d(d+2)\) for the negative round-sphere Casimir. -/
theorem sphereHarmonicBasisFunction_casimir (d : ℕ) (i : Fin ((d + 1)^2))
    (x : RoundSphere3) :
    planeRotationCasimir
      (spherePolynomialValue
        ((sphereHarmonicPolynomialBasis d i : SphereHomogeneous d) : SpherePolynomial)) x =
      -((d : ℝ) * ((d : ℝ) + 2)) * sphereHarmonicBasisFunction d i x := by
  let P : sphereHarmonicSubmodule d := sphereHarmonicPolynomialBasis d i
  have hp : polynomialLaplacian ((P : SphereHomogeneous d) : SpherePolynomial) = 0 :=
    mem_sphereHarmonicSubmodule_iff.mp P.property
  exact planeRotationCasimir_harmonic_on_sphere
    (contDiff_infty.mp (spherePolynomialValue_contDiff ((P : SphereHomogeneous d) : SpherePolynomial)) 2)
    d (fun t _ y => sphereHomogeneousValue_smul d P.val t y) (fun y => by
      rw [spherePolynomialValue_laplacian, hp]
      simp [spherePolynomialValue]) x

end Burnett.A06
