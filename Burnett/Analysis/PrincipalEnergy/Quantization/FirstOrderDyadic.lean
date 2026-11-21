import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators ContDiff FourierTransform Topology

private theorem scale_pos (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

/-- The dyadic scales are allowed to have different Schwartz profiles, as
occurs when the first-order symbol is neither homogeneous nor translation invariant. -/
theorem scaledFamily_absoluteSum_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (p : ℕ → SchwartzMap E F) (d : ℕ) (hd : 0 < d) (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ j, SchwartzMap.seminorm ℝ 0 0 (p j) ≤ C ∧
      SchwartzMap.seminorm ℝ (d + 1) 0 (p j) ≤ C)
    (z : E) (hz : z ≠ 0) :
    Summable (fun j => ‖dyadicScale j ^ d • p j (dyadicScale j • z)‖) ∧
      (∑' j, ‖dyadicScale j ^ d • p j (dyadicScale j • z)‖) ≤
        C * ((2 : ℝ) ^ d + 2) * (‖z‖ ^ d)⁻¹ := by
  let r := ‖z‖
  let b (j : ℕ) := ‖dyadicScale j ^ d • p j (dyadicScale j • z)‖
  let a (j : ℕ) := r ^ d * b j
  have hr : 0 < r := norm_pos_iff.mpr hz
  have hrpow : r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
  have hL (j : ℕ) : a j ≤ C * (dyadicScale j * r) ^ d := by
    unfold a b
    rw [norm_smul, Real.norm_of_nonneg (pow_nonneg (scale_pos j).le _), mul_pow]
    calc
      r ^ d * (dyadicScale j ^ d * ‖p j (dyadicScale j • z)‖) ≤
        r ^ d * (dyadicScale j ^ d * C) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
            ((SchwartzMap.norm_le_seminorm ℝ (p j) _).trans (hBound j).1)
            (pow_nonneg (scale_pos j).le _)) (pow_nonneg hr.le _)
      _ = _ := by ring
  have hH (j : ℕ) : a j ≤ C / (dyadicScale j * r) := by
    calc
      a j ≤ r ^ d * (SchwartzMap.seminorm ℝ (d+1) 0 (p j) * (dyadicScale j)⁻¹ *
          (r ^ (d+1))⁻¹) := mul_le_mul_of_nonneg_left
            (scaledSchwartz_high_bound (p j) d j z hz) (pow_nonneg hr.le _)
      _ ≤ r ^ d * (C * (dyadicScale j)⁻¹ * (r ^ (d+1))⁻¹) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hBound j).2 (inv_nonneg.mpr (scale_pos j).le))
            (inv_nonneg.mpr (pow_nonneg hr.le _))) (pow_nonneg hr.le _)
      _ = _ := by
        rw [pow_succ r]
        field_simp [hr.ne', (scale_pos j).ne', hrpow]
  obtain ⟨hSum, hSize⟩ := normalizedDyadicSeries_le d hd r C hr hC a
    (fun j => mul_nonneg (pow_nonneg hr.le _) (norm_nonneg _)) hL hH
  have hu : (fun j => ‖dyadicScale j ^ d • p j (dyadicScale j • z)‖) =
      fun j => (r ^ d)⁻¹ * a j := by
    funext j
    change b j = (r ^ d)⁻¹ * (r ^ d * b j)
    rw [← mul_assoc, inv_mul_cancel₀ hrpow, one_mul]
  rw [hu, tsum_mul_left]
  exact ⟨hSum.mul_left _, (mul_le_mul_of_nonneg_left hSize
    (inv_nonneg.mpr (pow_nonneg hr.le _))).trans_eq (mul_comm _ _)⟩

def normalizedFirstOrderAnnulus (a : E → E → ℂ) (x : E) (j : ℕ) (η : E) : ℂ :=
  (dyadicScale j)⁻¹ • ((annulus η : ℂ) * a x (dyadicScale j • η))

def firstOrderAnnularKernel (a : E → E → ℂ) (x : E) (j : ℕ) (z : E) : ℂ :=
  𝓕⁻ (fun ξ => (annulus ((dyadicScale j)⁻¹ • ξ) : ℂ) * a x ξ) z

/-- The extra scale in the fifth power is exactly the symbol order. -/
theorem firstOrderAnnularKernel_eq_scaled (a : E → E → ℂ) (x : E) (j : ℕ) (z : E) :
    firstOrderAnnularKernel a x j z =
      dyadicScale j ^ 5 • 𝓕⁻ (normalizedFirstOrderAnnulus a x j) (dyadicScale j • z) := by
  let s := dyadicScale j
  let q (η : E) := (annulus η : ℂ) * a x (s • η)
  have hs : s ≠ 0 := (scale_pos j).ne'
  have hq : (fun ξ => (annulus (s⁻¹ • ξ) : ℂ) * a x ξ) = fun ξ => q (s⁻¹ • ξ) := by
    funext ξ
    simp only [q, smul_smul, mul_inv_cancel₀ hs, one_smul]
  unfold firstOrderAnnularKernel
  change 𝓕⁻ (fun ξ => (annulus (s⁻¹ • ξ) : ℂ) * a x ξ) z = s ^ 5 • 𝓕⁻ (s⁻¹ • q) (s • z)
  have hSmul : 𝓕⁻ (s⁻¹ • q) (s • z) = s⁻¹ • 𝓕⁻ q (s • z) := by
    simp only [Real.fourierIntegralInv_eq, Pi.smul_apply, smul_comm _ (s⁻¹), MeasureTheory.integral_smul]
  rw [hq, inverseFourier_dilation s (scale_pos j), hSmul]
  have hPow : s ^ 5 * s⁻¹ = s ^ 4 := by
    rw [pow_succ, mul_assoc, mul_inv_cancel₀ hs, mul_one]
  rw [smul_smul, hPow]

def firstOrderKernel (a : E → E → ℂ) (x z : E) : ℂ :=
  ∑' j, firstOrderAnnularKernel a x j z

/-- Uniformity is in both the base variable and the annular index. -/
theorem firstOrderKernel_size (a : E → E → ℂ) (p : E → ℕ → SchwartzMap E ℂ)
    (hp : ∀ x j, (p x j : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus a x j))
    (C : ℝ) (hC : 0 ≤ C)
    (hBound : ∀ x j, SchwartzMap.seminorm ℝ 0 0 (p x j) ≤ C ∧
      SchwartzMap.seminorm ℝ 6 0 (p x j) ≤ C)
    (x z : E) (hz : z ≠ 0) :
    Summable (fun j => ‖firstOrderAnnularKernel a x j z‖) ∧
      ∀ N : ℕ, ‖∑ j ∈ Finset.range N, firstOrderAnnularKernel a x j z‖ ≤
        34 * C * (‖z‖ ^ 5)⁻¹ ∧ ‖firstOrderKernel a x z‖ ≤ 34 * C * (‖z‖ ^ 5)⁻¹ := by
  obtain ⟨hs, hb⟩ := scaledFamily_absoluteSum_le (p x) 5 (by decide) C hC (hBound x) z hz
  have hA (j : ℕ) : dyadicScale j ^ 5 • p x j (dyadicScale j • z) =
      firstOrderAnnularKernel a x j z := by
    rw [firstOrderAnnularKernel_eq_scaled, ← hp x j]
  simp only [hA] at hs hb
  have hS : C * ((2 : ℝ) ^ 5 + 2) = 34 * C := by ring
  rw [hS] at hb
  refine ⟨hs, fun N => ⟨?_, (norm_tsum_le_tsum_norm hs).trans hb⟩⟩
  exact (norm_sum_le _ _).trans ((hs.sum_le_tsum _ (fun _ _ => norm_nonneg _)).trans hb)

end Burnett.Analysis.FirstOrderDyadic
