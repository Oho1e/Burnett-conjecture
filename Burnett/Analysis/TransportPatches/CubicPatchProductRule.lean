import Burnett.Analysis.TransportPatches.ScaledCubicPartition
import Mathlib.Analysis.Calculus.FDeriv.Pow

/-! Exact product rule for a complete cubed partition applied to a
principal trilinear density with two differentiated slots. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.C01

open Filter Set Function Burnett.Analysis.CarlesonEmbedding
open scoped BigOperators Topology

/-- On the neighborhood with a cube partition, differentiating the
normalization makes the one-cutoff-derivative coefficient vanish. -/
theorem cubed_partition_first_derivative_zero {J : Type*} (s : Finset J)
    (χ : J → LatticeSpace → ℝ) (x v : LatticeSpace)
    (hχ : ∀ j ∈ s, DifferentiableAt ℝ (χ j) x)
    (hOne : (fun y => ∑ j ∈ s, χ j y ^ 3) =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    (∑ j ∈ s, χ j x ^ 2 * fderiv ℝ (χ j) x v) = 0 := by
  have hEach (j : J) (hj : j ∈ s) : HasFDerivAt (fun y => χ j y ^ 3)
      (((3 : ℝ) * χ j x ^ 2) • fderiv ℝ (χ j) x) x := by
    simpa only [show (3 : ℕ) - 1 = 2 by decide, nsmul_eq_mul, Nat.cast_ofNat] using
      (hχ j hj).hasFDerivAt.pow 3
  have hSum := (HasFDerivAt.fun_sum hEach).fderiv
  rw [hOne.fderiv_eq, fderiv_const_apply] at hSum
  have hEval := congrArg (fun D : LatticeSpace →L[ℝ] ℝ => D v) hSum.symm
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul,
    ContinuousLinearMap.zero_apply, mul_assoc, ← Finset.mul_sum] at hEval
  exact (mul_eq_zero.mp hEval).resolve_left (by norm_num)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem localize_fderiv_apply (χ : LatticeSpace → ℝ) (u : LatticeSpace → V)
    (x d : LatticeSpace) (hχ : DifferentiableAt ℝ χ x) (hu : DifferentiableAt ℝ u x) :
    fderiv ℝ (fun y => χ y • u y) x d =
      χ x • fderiv ℝ u x d + (fderiv ℝ χ x d) • u x := by
  change fderiv ℝ (χ • u) x d = _
  rw [fderiv_smul hχ hu]
  rfl

/-- For the same finite cutoff family in all three slots, the original
pointwise density plus the explicit two-cutoff-derivative remainder is
the exact sum of the localized densities. This is the local product
calculation before commuting the nonlocal test through the cutoffs. -/
theorem sum_cubed_patch_trilinear_density {J : Type*} (s : Finset J)
    (χ : J → LatticeSpace → ℝ)
    (L : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (u v w : LatticeSpace → V)
    (x d₁ d₂ : LatticeSpace) (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (hχ : ∀ j ∈ s, DifferentiableAt ℝ (χ j) x)
    (hOne : (fun y => ∑ j ∈ s, χ j y ^ 3) =ᶠ[𝓝 x] (fun _ => (1 : ℝ))) :
    (∑ j ∈ s, L (fderiv ℝ (fun y => χ j y • u y) x d₁)
      (fderiv ℝ (fun y => χ j y • v y) x d₂) (χ j x • w x)) =
      L (fderiv ℝ u x d₁) (fderiv ℝ v x d₂) (w x) +
        (∑ j ∈ s, χ j x * fderiv ℝ (χ j) x d₁ * fderiv ℝ (χ j) x d₂) *
          L (u x) (v x) (w x) := by
  have hD₁ := cubed_partition_first_derivative_zero s χ x d₁ hχ hOne
  have hD₂ := cubed_partition_first_derivative_zero s χ x d₂ hχ hOne
  calc
    _ = ∑ j ∈ s,
        (χ j x ^ 3 * L (fderiv ℝ u x d₁) (fderiv ℝ v x d₂) (w x) +
          (χ j x ^ 2 * fderiv ℝ (χ j) x d₁) * L (u x) (fderiv ℝ v x d₂) (w x) +
          (χ j x ^ 2 * fderiv ℝ (χ j) x d₂) * L (fderiv ℝ u x d₁) (v x) (w x) +
          (χ j x * fderiv ℝ (χ j) x d₁ * fderiv ℝ (χ j) x d₂) * L (u x) (v x) (w x)) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [localize_fderiv_apply _ _ x d₁ (hχ j hj) hu,
        localize_fderiv_apply _ _ x d₂ (hχ j hj) hv]
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_mul, hD₁, hD₂, hOne.eq_of_nhds,
        one_mul, zero_mul, add_zero]

end Burnett.C01
