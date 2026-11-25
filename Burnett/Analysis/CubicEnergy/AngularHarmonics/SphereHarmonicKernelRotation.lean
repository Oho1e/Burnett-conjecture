import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicRotationPolynomial
import Burnett.Analysis.CubicEnergy.AngularHarmonics.SphereHarmonicRotationEnergy

set_option autoImplicit false
set_option maxHeartbeats 7500000

noncomputable section

namespace Burnett.A06

open MvPolynomial Metric MeasureTheory
open scoped BigOperators ContDiff ENNReal

local instance : CompactSpace RoundSphere3 := Metric.sphere.compactSpace _ _
local instance : IsFiniteMeasure roundSphere3Measure :=
  inferInstanceAs (IsFiniteMeasure ((volume : Measure RotationSpace).toSphere))
local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩

/-- The actual ambient polynomial function behind the normalized harmonic. -/
def sphereHarmonicAmbientBasis (d : ℕ) (k : Fin ((d + 1)^2)) (x : RotationSpace) : ℝ :=
  spherePolynomialValue (sphereHarmonicPolynomialBasis d k).val.val x

def sphereHarmonicKernelDiagonal (d : ℕ) (x : RotationSpace) : ℝ :=
  ∑ k : Fin ((d + 1)^2), sphereHarmonicAmbientBasis d k x ^ 2

private def harmonicEvaluation (d : ℕ) (x : RotationSpace) : sphereHarmonicSubmodule d →ₗ[ℝ] ℝ where
  toFun H := spherePolynomialValue H.val.val x
  map_add' P Q := map_add (eval fun i => x i) P.val.val Q.val.val
  map_smul' a P := by
    change eval (fun i => x i) (a • P.val.val) = a * eval (fun i => x i) P.val.val
    rw [smul_eq_C_mul, map_mul, eval_C]

def sphereHarmonicReproducingPolynomial (d : ℕ) (x : RotationSpace) : sphereHarmonicSubmodule d :=
  ∑ k : Fin ((d + 1)^2), sphereHarmonicAmbientBasis d k x • sphereHarmonicPolynomialBasis d k

/-- Actual real evaluation on the homogeneous harmonic subspace is given by a
vector in that same subspace, with its true sphere L² pairing. -/
theorem sphereHarmonicValue_eq_reproducing_inner (d : ℕ) (x : RotationSpace)
    (H : sphereHarmonicSubmodule d) :
    spherePolynomialValue H.val.val x =
      inner ℝ (sphereHarmonicToLp d (sphereHarmonicReproducingPolynomial d x)) (sphereHarmonicToLp d H) := by
  let K := sphereHarmonicReproducingPolynomial d x
  let L := ((innerSL ℝ (sphereHarmonicToLp d K)).toLinearMap).comp (sphereHarmonicToLp d)
  have eq : harmonicEvaluation d x = L := by
    apply (sphereHarmonicPolynomialBasis d).ext
    intro k
    have eqLp (i : Fin ((d + 1)^2)) :
        sphereHarmonicToLp d (sphereHarmonicPolynomialBasis d i) =
          (sphereHarmonicLpOrthonormalBasis d i : RoundSphereL2) :=
      sphereHarmonicBasisFunction_toLp d i
    have hInner (i j : Fin ((d + 1)^2)) :
        inner ℝ (sphereHarmonicLpOrthonormalBasis d i : RoundSphereL2)
          (sphereHarmonicLpOrthonormalBasis d j : RoundSphereL2) = if i = j then 1 else 0 :=
      (sphereHarmonicLpOrthonormalBasis d).inner_eq_ite i j
    change sphereHarmonicAmbientBasis d k x =
      inner ℝ (sphereHarmonicToLp d
        (∑ i : Fin ((d + 1)^2), sphereHarmonicAmbientBasis d i x • sphereHarmonicPolynomialBasis d i))
        (sphereHarmonicToLp d (sphereHarmonicPolynomialBasis d k))
    rw [map_sum, sum_inner]
    simp only [map_smul, eqLp, real_inner_smul_left, hInner, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
  exact congrArg (fun A : sphereHarmonicSubmodule d →ₗ[ℝ] ℝ => A H) eq

theorem sphereHarmonicKernelDiagonal_eq_L2_sq (d : ℕ) (x : RotationSpace) :
    sphereHarmonicKernelDiagonal d x =
      ‖sphereHarmonicToLp d (sphereHarmonicReproducingPolynomial d x)‖ ^ 2 := by
  let H := sphereHarmonicReproducingPolynomial d x
  rw [← real_inner_self_eq_norm_sq, ← sphereHarmonicValue_eq_reproducing_inner]
  change sphereHarmonicKernelDiagonal d x = harmonicEvaluation d x H
  simp only [H, sphereHarmonicReproducingPolynomial, map_sum, map_smul, smul_eq_mul]
  unfold sphereHarmonicKernelDiagonal
  apply Finset.sum_congr rfl
  intro i _
  exact pow_two _

private theorem sphereHarmonicRotation_inner_self (d : ℕ) (H : sphereHarmonicSubmodule d) (i j : Fin 4) :
    inner ℝ (sphereHarmonicToLp d H) (sphereHarmonicToLp d (sphereHarmonicPolynomialRotation d i j H)) = 0 := by
  let f := spherePolynomialValue H.val.val
  have hf : ContDiff ℝ 1 f := contDiff_infty.mp (spherePolynomialValue_contDiff _) 1
  rw [show sphereHarmonicToLp d H = ContinuousMap.toLp 2 roundSphere3Measure ℝ
    (sphereHomogeneousRestriction d H.val) from rfl,
    show sphereHarmonicToLp d (sphereHarmonicPolynomialRotation d i j H) =
      ContinuousMap.toLp 2 roundSphere3Measure ℝ (sphereHomogeneousRestriction d
        (sphereHarmonicPolynomialRotation d i j H).val) from rfl,
    ContinuousMap.inner_toLp]
  change (∫ x : RoundSphere3, spherePolynomialValue (rotationalPolynomial i j H.val.val) x * f x
    ∂roundSphere3Measure) = 0
  rw [spherePolynomialValue_rotationalPolynomial]
  by_cases heq : i = j
  · subst j
    simp [planeRotationDerivative_eq_coordinates]
  · have ha := integral_planeRotationDerivative_mul heq hf hf
    have hb : (∫ x : RoundSphere3, f x * planeRotationDerivative i j f x ∂roundSphere3Measure) =
        ∫ x : RoundSphere3, planeRotationDerivative i j f x * f x ∂roundSphere3Measure := by
      simp only [mul_comm]
    rw [hb] at ha
    linarith only [ha]

theorem sphereHarmonicKernelDiagonal_contDiff (d : ℕ) :
    ContDiff ℝ ∞ (sphereHarmonicKernelDiagonal d) := by
  unfold sphereHarmonicKernelDiagonal
  exact ContDiff.sum (fun k _ => (spherePolynomialValue_contDiff
    (sphereHarmonicPolynomialBasis d k).val.val).pow 2)

/-- Infinitesimal rotation invariance of the exact diagonal reproducing kernel
of the real degree-d harmonic subspace. -/
theorem planeRotationDerivative_sphereHarmonicKernelDiagonal (d : ℕ) (i j : Fin 4)
    (x : RotationSpace) : planeRotationDerivative i j (sphereHarmonicKernelDiagonal d) x = 0 := by
  let b := sphereHarmonicPolynomialBasis d
  let B := sphereHarmonicAmbientBasis d
  let K := sphereHarmonicReproducingPolynomial d x
  have hb (k : Fin ((d + 1)^2)) : Differentiable ℝ (B k) :=
    (contDiff_infty.mp (spherePolynomialValue_contDiff (b k).val.val) 1).differentiable_one
  have hpair := sphereHarmonicValue_eq_reproducing_inner d x (sphereHarmonicPolynomialRotation d i j K)
  rw [sphereHarmonicRotation_inner_self] at hpair
  have hv : planeRotationDerivative i j (spherePolynomialValue K.val.val) x = 0 := by
    rw [← spherePolynomialValue_rotationalPolynomial]
    exact hpair
  have hk : spherePolynomialValue K.val.val = fun y : RotationSpace =>
      ∑ k : Fin ((d + 1)^2), B k x * B k y := by
    funext y
    change harmonicEvaluation d y K = _
    simp [K, sphereHarmonicReproducingPolynomial, map_sum, map_smul, smul_eq_mul,
      harmonicEvaluation, B, sphereHarmonicAmbientBasis]
  rw [hk] at hv
  have hz :
      (∑ k : Fin ((d + 1)^2), B k x * planeRotationDerivative i j (B k) x) = 0 := by
    simpa only [planeRotationDerivative, fderiv_fun_sum (fun k _ => (hb k x).const_mul (B k x)),
      fderiv_const_mul (hb _ x), ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] using hv
  change fderiv ℝ (fun y : RotationSpace => ∑ k : Fin ((d + 1)^2), B k y ^ 2) x
    (planeRotationGenerator i j x) = 0
  have hb₂ (k : Fin ((d + 1)^2)) : DifferentiableAt ℝ (fun y => B k y ^ 2) x := (hb k x).pow 2
  rw [fderiv_fun_sum (fun k _ => hb₂ k), ContinuousLinearMap.sum_apply]
  have ht (k : Fin ((d + 1)^2)) :
      fderiv ℝ (fun y => B k y ^ 2) x (planeRotationGenerator i j x) =
        2 * (B k x * planeRotationDerivative i j (B k) x) := by
    simp only [pow_two, show (fun y => B k y * B k y) = B k * B k from rfl,
      fderiv_mul (hb k x) (hb k x), ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, planeRotationDerivative]
    ring
  simp_rw [ht]
  rw [← Finset.mul_sum, hz, mul_zero]

end Burnett.A06
