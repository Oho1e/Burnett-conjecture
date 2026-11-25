import Burnett.Analysis.AllScaleTransfer.JointCubeFourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option maxHeartbeats 2450000
noncomputable section

namespace Burnett.A05.BoxFourier

open MeasureTheory Set Filter
open scoped ContDiff FourierTransform ENNReal

def boxDecayConstant (P : ℝ) : ℝ :=
  max 1 (3^40 * ((2 * P)^40 * (2^40 * 41)))

private theorem norm_integral_jet_le (P : ℝ) (hP : 0 < P) (f : BoxSpace → ℂ)
    (hs : tsupport f ⊆ boxFourierCube P) (n : ℕ) (M : ℝ)
    (hM : ∀ z ∈ boxFourierCube P, ‖iteratedFDeriv ℝ n f z‖ ≤ M) :
    (∫ y : BoxSpace, ‖iteratedFDeriv ℝ n f y‖) ≤ M * (2 * P)^8 := by
  have he (y : BoxSpace) (hy : y ∉ boxFourierCube P) : ‖iteratedFDeriv ℝ n f y‖ = 0 := by
    rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hs (tsupport_iteratedFDeriv_subset n h))),
      norm_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero he]
  have hf : (volume : Measure BoxSpace) (boxFourierCube P) < ⊤ := by
    rw [box_fourier_cube_volume]
    exact ENNReal.pow_lt_top ENNReal.ofReal_lt_top
  have hr : (volume : Measure BoxSpace).real (boxFourierCube P) = (2 * P)^8 := by
    rw [Measure.real, box_fourier_cube_volume, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]
  calc
    _ ≤ ‖∫ y in boxFourierCube P, ‖iteratedFDeriv ℝ n f y‖‖ := by
      rw [Real.norm_eq_abs]
      exact le_abs_self _
    _ ≤ _ := by
      rw [← hr]
      apply norm_setIntegral_le_of_norm_le_const_ae' hf
      exact Eventually.of_forall fun y hy => by simpa using hM y hy

/-- Forty finite Fréchet jets of the same compact profile control the
fortieth weighted power of its true eight-dimensional Fourier coefficient. -/
theorem joint_cube_coefficient_norm_pow_le (P : ℝ) (hP : 0 < P) (f : BoxSpace → ℂ)
    (hSmooth : ContDiff ℝ 40 f) (hCompact : HasCompactSupport f)
    (hs : tsupport f ⊆ boxFourierCube P) (M : ℝ)
    (bound : ∀ n ≤ 40, ∀ z ∈ boxFourierCube P, ‖iteratedFDeriv ℝ n f z‖ ≤ M)
    (k : BoxIndex → ℤ) :
    ‖boxLatticeVector k‖^40 * ‖boxCubeFourierCoefficient P k f‖ ≤
      ((2 * P)^40 * (2^40 * 41)) * M := by
  let ξ := boxModeFrequency P k
  let V := (2 * P)^8
  have hV : 0 < V := by dsimp [V]; positivity
  have hInt (j n : ℕ) (hj : j ≤ (0 : ℕ∞)) (hn : n ≤ (40 : ℕ∞)) :
      Integrable (fun y : BoxSpace => ‖y‖^j * ‖iteratedFDeriv ℝ n f y‖) := by
    obtain rfl : j = 0 := Nat.eq_zero_of_le_zero (by exact_mod_cast hj)
    simp only [pow_zero, one_mul]
    exact (hSmooth.continuous_iteratedFDeriv (by exact_mod_cast hn)).norm.integrable_of_hasCompactSupport
      (hCompact.iteratedFDeriv n).norm
  have hFourier := Real.pow_mul_norm_iteratedFDeriv_fourierIntegral_le
    (K := 0) (N := 40) (k := 0) (n := 40) hSmooth hInt (by simp) (by simp) ξ
  simp only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Nat.cast_zero, mul_zero, zero_add] at hFourier
  have hSum :
      (∑ p ∈ Finset.range (0 + 1) ×ˢ Finset.range (40 + 1),
        ∫ y : BoxSpace, ‖y‖^p.1 * ‖iteratedFDeriv ℝ p.2 f y‖) ≤ 41 * (M * V) := by
    calc
      _ ≤ ∑ _p ∈ Finset.range (0 + 1) ×ˢ Finset.range (40 + 1), M * V := by
        apply Finset.sum_le_sum
        intro p hp
        have h0 : p.1 = 0 := by simpa using (Finset.mem_product.mp hp).1
        have h40 : p.2 ≤ 40 := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_product.mp hp).2)
        simpa only [h0, pow_zero, one_mul] using norm_integral_jet_le P hP f hs p.2 M (bound p.2 h40)
      _ = _ := by simp [nsmul_eq_mul]
  have hWeight : ‖ξ‖ ^ 40 * ‖𝓕 f ξ‖ ≤ (2 : ℝ)^40 * (41 * (M * V)) :=
    hFourier.trans (mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ (2 : ℝ)^40))
  have hz (y : BoxSpace) (hy : y ∉ boxFourierCube P) : f y = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hy (hs h))
  have hCoeff : ‖ξ‖ ^ 40 * ‖boxCubeFourierCoefficient P k f‖ ≤ (2 : ℝ)^40 * 41 * M := by
    rw [box_cube_fourier_coefficient_eq_fourier P k f hz, norm_smul,
      Real.norm_of_nonneg (inv_nonneg.mpr hV.le)]
    change ‖ξ‖ ^ 40 * (V⁻¹ * ‖𝓕 f ξ‖) ≤ _
    calc
      _ = V⁻¹ * (‖ξ‖ ^ 40 * ‖𝓕 f ξ‖) := by ring
      _ ≤ V⁻¹ * ((2 : ℝ)^40 * (41 * (M * V))) :=
        mul_le_mul_of_nonneg_left hWeight (inv_nonneg.mpr hV.le)
      _ = _ := by field_simp [hV.ne']
  have hFreq : (2 * P)^40 * ‖ξ‖^40 = ‖boxLatticeVector k‖^40 := by
    rw [← mul_pow]
    congr 1
    dsimp [ξ, boxModeFrequency]
    rw [norm_smul, Real.norm_of_nonneg (by positivity), ← mul_assoc, mul_inv_cancel₀ (by positivity),
      one_mul]
  calc
    _ = (2 * P)^40 * (‖ξ‖^40 * ‖boxCubeFourierCoefficient P k f‖) := by rw [← mul_assoc, hFreq]
    _ ≤ _ := by
      rw [mul_assoc ((2 * P)^40)]
      exact mul_le_mul_of_nonneg_left hCoeff (by positivity)

end Burnett.A05.BoxFourier
