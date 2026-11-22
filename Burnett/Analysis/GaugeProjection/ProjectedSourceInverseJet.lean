import Burnett.Analysis.GaugeProjection.ProjectedCoordinateRicci
import Mathlib.Data.Matrix.Mul

set_option autoImplicit false
set_option maxHeartbeats 2700000

noncomputable section

namespace Burnett.P01

open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Matrix Filter
open scoped BigOperators Topology

/-- The coordinate derivative of the same inverse metric field is a product
of the two inverse metrics and the first derivative of the metric. -/
theorem coordinateJet_inverse_eq_neg
    (g inv : CoordinateSpace → Tensor2) (x : CoordinateSpace)
    (hg : DifferentiableComponentsAt g x) (hi : DifferentiableComponentsAt inv x)
    (hLeft : ∀ᶠ y in 𝓝 x, ∀ a b, (∑ k, inv y a k * g y k b) = if a = b then 1 else 0)
    (hRight : ∀ a b, (∑ k, g x a k * inv x k b) = if a = b then 1 else 0)
    (i : Index) :
    Matrix.of (coordinateJet inv x i) =
      -(Matrix.of (inv x) * Matrix.of (coordinateJet g x i) * Matrix.of (inv x)) := by
  let A : Matrix Index Index ℝ := inv x
  let G : Matrix Index Index ℝ := g x
  let dA : Matrix Index Index ℝ := coordinateJet inv x i
  let dG : Matrix Index Index ℝ := coordinateJet g x i
  have hGA : G * A = 1 := by
    ext a b
    simpa only [G, A, Matrix.mul_apply, Matrix.one_apply] using hRight a b
  have hDer : dA * G + A * dG = 0 := by
    ext a b
    have heq : (fun y => ∑ k, inv y a k * g y k b) =ᶠ[𝓝 x]
        (fun _ : CoordinateSpace => if a = b then (1 : ℝ) else 0) :=
      hLeft.mono (fun y hy => hy a b)
    have hz : fderiv ℝ (fun y => ∑ k, inv y a k * g y k b) x = 0 := by
      rw [heq.fderiv_eq]
      exact (hasFDerivAt_const (𝕜 := ℝ) (if a = b then (1 : ℝ) else 0) x).fderiv
    have point (k : Index) :
        fderiv ℝ (fun y => inv y a k * g y k b) x (EuclideanSpace.single i 1) =
          dA a k * G k b + A a k * dG k b := by
      rw [((hi a k).hasFDerivAt.fun_mul (hg k b).hasFDerivAt).fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
        smul_eq_mul, dA, dG, A, G, coordinateJet]
      ring
    have hTerms : ∀ k ∈ (Finset.univ : Finset Index),
        DifferentiableAt ℝ (fun y : CoordinateSpace => inv y a k * g y k b) x :=
      fun k _ => (hi a k).mul (hg k b)
    rw [fderiv_fun_sum hTerms] at hz
    have dp := congrArg (fun L : CoordinateSpace →L[ℝ] ℝ => L (EuclideanSpace.single i 1)) hz
    simp only [ContinuousLinearMap.sum_apply, point, ContinuousLinearMap.zero_apply, Finset.sum_add_distrib] at dp
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.zero_apply] using dp
  have hAG : dA * G = -(A * dG) := eq_neg_of_add_eq_zero_left hDer
  change dA = -(A * dG * A)
  calc
    dA = dA * (G * A) := by simp only [hGA, mul_one]
    _ = (dA * G) * A := (mul_assoc _ _ _).symm
    _ = _ := by rw [hAG, neg_mul]

end Burnett.P01
