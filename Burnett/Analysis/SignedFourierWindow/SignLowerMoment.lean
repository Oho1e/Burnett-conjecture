import Burnett.Analysis.SignedFourierWindow.SignAverage

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.DyadicSquare hiding Space
open Finset

private theorem avg_nonneg {n : ℕ} {F : (Fin n → Bool) → ℝ} (h : ∀ s, 0 ≤ F s) : 0 ≤ signAverage n F :=
  (signAverage_const n 0).symm.trans_le (signAverage_mono h)

/-- A quantitative lower Khintchine inequality for complex coefficients. The
second and fourth moments give a fixed positive probability of a large sum. -/
theorem square_le_sign_moment {n : ℕ} (v : Fin n → ℂ) (p : ℝ) (hp : 0<p) :
    (Real.sqrt (vectorEnergy v))^p ≤ (24*(2:ℝ)^p) * signAverage n (fun s => ‖signedVector v s‖^p) := by
  let m := Real.sqrt (vectorEnergy v)
  let u := fun s => ‖signedVector v s‖/m
  have nonneg : 0 ≤ vectorEnergy v := sum_nonneg (fun _ _ => sq_nonneg _)
  have msq : m^2 = vectorEnergy v := Real.sq_sqrt nonneg
  obtain ⟨second,fourth⟩ := sign_moments v
  by_cases mz : m=0
  · change m^p ≤ _
    rw [mz,Real.zero_rpow hp.ne']
    exact mul_nonneg (by positivity) (avg_nonneg fun s => Real.rpow_nonneg (norm_nonneg _) _)
  have mp : 0<m := lt_of_le_of_ne (Real.sqrt_nonneg _) (Ne.symm mz)
  have n₂ : signAverage n (fun s => (u s)^2) = 1 := by
    simp only [u,div_eq_inv_mul,mul_pow,inv_pow,signAverage_mul,second]
    rw [← msq,inv_mul_cancel₀ (pow_ne_zero _ mz)]
  have n₄ : signAverage n (fun s => (u s)^4) ≤ 3 := by
    simp only [u,div_eq_inv_mul,mul_pow,inv_pow,signAverage_mul]
    rw [← msq] at fourth
    apply (inv_mul_le_iff₀ (pow_pos mp 4)).mpr
    exact fourth.trans_eq (by ring)
  let C := 12*(2:ℝ)^p
  have Cp : 0 ≤ C := by dsimp only [C]; positivity
  have scalar (t : ℝ) (ht : 0≤t) : t^2 ≤ 1/4+C*t^p+(1/12)*t^4 := by
    have pos := mul_nonneg Cp (Real.rpow_nonneg ht p)
    by_cases small : t ≤ 1/2
    · nlinarith [mul_nonneg (by linarith : 0≤(1:ℝ)/2-t) (by linarith : 0≤(1:ℝ)/2+t),sq_nonneg (t^2)]
    by_cases big : 12 ≤ t^2
    · nlinarith [mul_nonneg (sub_nonneg.mpr big) (sq_nonneg t)]
    have pow : 1 ≤ (2*t)^p := Real.one_le_rpow (by linarith) hp.le
    rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) ht] at pow
    dsimp only [C] at *
    nlinarith [sq_nonneg (t^2)]
  have major := signAverage_mono (fun s => scalar (u s) (div_nonneg (norm_nonneg _) mp.le))
  simp only [signAverage_add,signAverage_const,signAverage_mul,n₂] at major
  have lower : 1 ≤ (24*(2:ℝ)^p) * signAverage n (fun s => (u s)^p) := by
    dsimp only [C] at major
    nlinarith [major,n₄]
  have norm (s : Fin n → Bool) : (u s)^p = (m^p)⁻¹ * ‖signedVector v s‖^p := by
    rw [show u s = ‖signedVector v s‖/m from rfl,Real.div_rpow (norm_nonneg _) mp.le,div_eq_inv_mul]
  simp_rw [norm,signAverage_mul] at lower
  change m^p ≤ _
  have pos := Real.rpow_pos_of_pos mp p
  have eq : 24*2^p*((m^p)⁻¹*signAverage n (fun s => ‖signedVector v s‖^p)) =
      (24*2^p*signAverage n (fun s => ‖signedVector v s‖^p))/m^p := by ring
  rw [eq,le_div_iff₀ pos,one_mul] at lower
  exact lower

end Burnett.Analysis.SignedFourierWindow
