import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualParaproductResolution

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Set
open scoped BigOperators

private theorem inverse_power_wavelet_scale_shift (t : ℝ) (k : ℤ) (m n : ℕ) :
    ((bilateralWaveletScale t (k-(n:ℤ)))^m)⁻¹ =
      ((bilateralWaveletScale t k)^m)⁻¹ * (((2:ℝ)^m)⁻¹)^n := by
  have hScale : bilateralWaveletScale t (k-(n:ℤ)) = bilateralWaveletScale t k*(2:ℝ)^n := by
    rw [bilateralWaveletScale,bilateralWaveletScale,zpow_sub₀ (by norm_num),zpow_natCast,div_div_eq_mul_div]
    ring
  rw [hScale,mul_pow,mul_inv_rev,← pow_mul,Nat.mul_comm n m,pow_mul,← inv_pow]
  ring

/-- A sequence which vanishes below spatial scale $R$ and is dominated by
$A s^{-m}$ has a bilateral sum bounded by the exact geometric factor. -/
theorem bilateral_wavelet_inversePower_tail (m : ℕ) (hm : 0<m) (t R : ℝ)
    (ht : 0<t) (hR : 0<R) {A : ℝ} (hA : 0≤A) (f : ℤ → ℝ)
    (hf : ∀ j, 0≤f j)
    (hZero : ∀ j, bilateralWaveletScale t j<R → f j=0)
    (hBound : ∀ j, f j≤A*((bilateralWaveletScale t j)^m)⁻¹) :
    Summable f ∧ ‖∑' j, f j‖ ≤ A*(R^m)⁻¹*(1-((2:ℝ)^m)⁻¹)⁻¹ := by
  obtain ⟨k,hk⟩ := exists_mem_Ico_zpow (div_pos ht hR) (by norm_num : 1<(2:ℝ))
  have hPow (j : ℤ) : 0<(2:ℝ)^j := zpow_pos (by norm_num) _
  have hScale : R≤bilateralWaveletScale t k := by
    change R≤t/(2:ℝ)^k
    apply (le_div_iff₀ (hPow k)).mpr
    exact (mul_comm R ((2:ℝ)^k)).le.trans ((le_div_iff₀ hR).mp hk.1)
  have hFine (j : ℤ) (hj : k<j) : f j=0 := by
    apply hZero
    change t/(2:ℝ)^j<R
    have hp : t/R<(2:ℝ)^j := hk.2.trans_le (zpow_le_zpow_right₀ (by norm_num) (by omega))
    apply (div_lt_iff₀ (hPow j)).mpr
    exact ((div_lt_iff₀ hR).mp hp).trans_le (mul_comm ((2:ℝ)^j) R).le
  let q := ((2:ℝ)^m)⁻¹
  have hq₀ : 0≤q := inv_nonneg.mpr (pow_nonneg (by norm_num) _)
  have hq₁ : q<1 := inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) hm.ne')
  let g (j : ℤ) := f (k+1+j)
  let h (n : ℕ) := A*(R^m)⁻¹*q^n
  have hInv : ((bilateralWaveletScale t k)^m)⁻¹ ≤ (R^m)⁻¹ :=
    (inv_le_inv₀ (pow_pos (hR.trans_le hScale) _) (pow_pos hR _)).mpr (pow_le_pow_left₀ hR.le hScale _)
  have hGNat : (fun n : ℕ => g (n:ℤ)) = fun _ => 0 := by
    funext n
    dsimp only [g]
    exact hFine _ (by omega)
  have hNeg (n : ℕ) : g (-((n:ℤ)+1))≤h n := by
    change f (k+1 + -((n:ℤ)+1)) ≤ A*(R^m)⁻¹*q^n
    rw [show k+1 + -((n:ℤ)+1)=k-(n:ℤ) by omega]
    refine (hBound _).trans ?_
    rw [inverse_power_wavelet_scale_shift,← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hInv hA) (pow_nonneg hq₀ _)
  have hSNat : Summable (fun n : ℕ => g (n:ℤ)) := by rw [hGNat]; exact summable_zero
  have hSGeom : Summable h := (summable_geometric_of_lt_one hq₀ hq₁).mul_left _
  have hSNeg : Summable (fun n : ℕ => g (-((n:ℤ)+1))) :=
    Summable.of_nonneg_of_le (fun _ => hf _) hNeg hSGeom
  have hG : Summable g := Summable.of_nat_of_neg_add_one hSNat hSNeg
  let e : ℤ ≃ ℤ := Equiv.addLeft (k+1)
  have hSumF : Summable f := e.summable_iff.mp hG
  refine ⟨hSumF,?_⟩
  rw [Real.norm_of_nonneg (tsum_nonneg hf)]
  calc
    _ = ∑' j, g j := (e.tsum_eq f).symm
    _ = ∑' n : ℕ, g (-((n:ℤ)+1)) := by
      rw [tsum_of_nat_of_neg_add_one hSNat hSNeg,hGNat,tsum_zero,zero_add]
    _ ≤ ∑' n, h n := hSNeg.tsum_le_tsum hNeg hSGeom
    _ = _ := by dsimp only [h]; rw [tsum_mul_left,tsum_geometric_of_lt_one hq₀ hq₁]

end Burnett.Analysis.CarlesonEmbedding
