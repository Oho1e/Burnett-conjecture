import Burnett.Analysis.PrincipalEnergy.Freezing.FiniteModeEnergyLinearity

set_option autoImplicit false
set_option maxHeartbeats 3900000

noncomputable section

namespace Burnett.A03

open Filter Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped BigOperators Topology Burnett.A03

/-- The cubic partition cancels each single-cutoff-derivative contribution
for a complex scalar placement. Both remaining differentiated cutoffs
multiply undifferentiated field or test values. -/
theorem sum_cubed_patch_scalar_placement {K : Type*} (s : Finset K)
    (t d e : K → ℂ) (u v w U V : ℂ)
    (hCube : ∑ k ∈ s, t k ^ 3 = 1)
    (hFirst : ∑ k ∈ s, t k ^ 2 * d k = 0)
    (hSecond : ∑ k ∈ s, t k ^ 2 * e k = 0) :
    (∑ k ∈ s, (t k * u + d k * U) * (t k * v + e k * V) * (t k * w)) =
      u * v * w + (∑ k ∈ s, t k * d k * e k) * U * V * w := by
  classical
  calc
    _ = ∑ k ∈ s, (t k ^ 3 * (u * v * w) + (t k ^ 2 * d k) * (U * v * w) +
        (t k ^ 2 * e k) * (u * V * w) + (t k * d k * e k) * (U * V * w)) := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [← Finset.sum_mul, hCube, hFirst, hSecond, one_mul, zero_mul, add_zero]
      ring

/-- The complex scalar partition derived from the true finite cutoff
functions retains the derivative cancellation at the same point. -/
theorem cubed_partition_complex_first_derivative_zero {K : Type*} (s : Finset K)
    (χ : K → SchwartzMap E ℂ) (x : E) (a : Index)
    (hOne : (fun y => ∑ k ∈ s, χ k y ^ 3) =ᶠ[𝓝 x] fun _ : E => (1 : ℂ)) :
    ∑ k ∈ s, χ k x ^ 2 * energyPartial a (χ k) x = 0 := by
  classical
  have hEach (k : K) (_ : k ∈ s) : HasFDerivAt (fun y => χ k y ^ 3)
      (((3 : ℂ) * χ k x ^ 2) • fderiv ℝ (χ k : E → ℂ) x) x := by
    have h := (χ k).differentiable x
    simpa only [show (3 : ℕ) - 1 = 2 by decide, nsmul_eq_mul, Nat.cast_ofNat]
      using h.hasFDerivAt.pow 3
  have hSum := (HasFDerivAt.fun_sum hEach).fderiv
  rw [hOne.fderiv_eq, fderiv_const_apply] at hSum
  have hEval := congrArg (fun D : E →L[ℝ] ℂ => D (EuclideanSpace.single a 1)) hSum.symm
  have hZero : (3 : ℂ) * (∑ k ∈ s, χ k x ^ 2 * energyPartial a (χ k) x) = 0 := by
    change (3 : ℂ) * (∑ k ∈ s, χ k x ^ 2 * fderiv ℝ (χ k : E → ℂ) x (EuclideanSpace.single a 1)) = 0
    simpa only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
      ContinuousLinearMap.zero_apply, mul_assoc, ← Finset.mul_sum] using hEval
  exact (mul_eq_zero.mp hZero).resolve_left (by norm_num)

end Burnett.A03
