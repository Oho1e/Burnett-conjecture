import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionNormalized

set_option autoImplicit false
set_option maxHeartbeats 4100000

noncomputable section

namespace Burnett.A05

open Finset
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier

def lowPassCorrectionShifts (C H : ℕ) : Finset ℤ :=
  Finset.Icc (-((C : ℤ)+1)) (H : ℤ)

/-- Factor one true normalized box block into the exact correction at j
and the additional first-input annulus and signed third window. -/
theorem radianLowPassCorrectionBlock_factor (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (M₀ : Joint → ℂ) (d : SchwartzMap E ℂ) (k j : ℤ) (p : Joint) :
    radianFixedShiftBoxBlock d (normalizedLowPassCorrection χ₀ A C M₀ k) k j p =
      radianLowPassCorrectionBlock χ₀ A C M₀ j p *
        ((integerRadialWindow (j+k) p.1 : ℂ) * d ((2 : ℝ)^(-j) • (-(p.1+p.2)))) := by
  unfold radianFixedShiftBoxBlock radianLowPassCorrectionBlock
  rw [normalizedLowPassCorrection_at_frequencies]
  ring

/-- The original low-pass correction at each actual second-slot index is
exactly the finite sum of signed first-slot annuli with the retained third window. -/
theorem exists_lowPassCorrection_fixedShift_partition {χ₀ : ℝ → ℝ}
    (L U l u : ℝ) (hL : 0 < L) (hU : 0 < U) (hl : 0 < l) (hu : 0 ≤ u) (hu1 : u < 1)
    (hOne : ∀ t, 0 ≤ t → t ≤ l → χ₀ t = 1) (hZero : ∀ t, u ≤ t → χ₀ t = 0) :
    ∃ C H : ℕ, 3 ≤ C ∧ 4*(U/L)/(2 : ℝ)^C ≤ l ∧
      ∀ (A : E ≃L[ℝ] E), (∀ x : E, ‖A x‖ ≤ U*‖x‖) →
      ∀ M₀ : Joint → ℂ,
      (∀ (j : ℤ) (p : Joint), radianLowPassCorrectionBlock χ₀ A C M₀ j p ≠ 0 →
        L*‖p.1‖ ≤ ‖A p.1‖ ∧ L*‖p.2‖ ≤ ‖A p.2‖) →
      ∀ (j : ℤ) (p : Joint),
        let d := lowPassCorrectionThirdProfile L U u hL hU hu1
        (∑ k ∈ lowPassCorrectionShifts C H,
          radianFixedShiftBoxBlock d (normalizedLowPassCorrection χ₀ A C M₀ k) k j p) =
          radianLowPassCorrectionBlock χ₀ A C M₀ j p := by
  obtain ⟨C,H,hC,hThin,hBound⟩ := exists_radialRatioCorrection_finiteShifts
    (div_pos hL hU) (div_pos hU hL) hl hOne hZero
  refine ⟨C,H,hC,hThin,?_⟩
  intro A hUpper M₀ hInput j p d
  by_cases hzero : radianLowPassCorrectionBlock χ₀ A C M₀ j p = 0
  · simp only [radianLowPassCorrectionBlock_factor, hzero, zero_mul, Finset.sum_const_zero]
  obtain ⟨hp,hq⟩ := hInput j p hzero
  have hHigh : integerRadialWindow j p.2 ≠ 0 := by
    intro h
    apply hzero
    simp only [radianLowPassCorrectionBlock, h, Complex.ofReal_zero, zero_mul, mul_zero]
  have hDiff : lowPassCorrectionDifference χ₀ A C j p.1 p.2 ≠ 0 := by
    intro h
    apply hzero
    simp only [radianLowPassCorrectionBlock, h, Complex.ofReal_zero, mul_zero]
  have hr : 0 < (2 : ℝ)^j := by positivity
  have hqBand := radialAnnularCutoff_nonzero hr hHigh
  have hCompare := physical_ratio_compare_of_uniform_norms A hL hU
    ((show 0 < (2 : ℝ)^j/2 by positivity).trans hqBand.1) ⟨hp,hUpper p.1⟩ ⟨hq,hUpper p.2⟩
  have hActive := (hBound ((2 : ℝ)^j) hr p.1 p.2 (‖A p.1‖/‖A p.2‖)
    ⟨hqBand.1.le,hqBand.2.le⟩ hCompare.1 hCompare.2).2.2 hDiff
  have hp0 : p.1 ≠ 0 := by
    intro h
    have impossible : (L/U)/(2*(2 : ℝ)^C) < 0 := by
      simpa only [h, map_zero, norm_zero, zero_div] using hActive.1
    exact (not_lt_of_ge (by positivity)) impossible
  have hThird : d ((2 : ℝ)^(-j) • (-(p.1+p.2))) = 1 :=
    lowPassCorrectionThirdProfile_at_dyadic A hL hU hu hu1 hUpper hp hq j
      ⟨hqBand.1.le,hqBand.2.le⟩ hActive.2.1
  let I := lowPassCorrectionShifts C H
  have outside (k : ℤ) (hk : k ∉ I) : integerRadialWindow (j+k) p.1 = 0 := by
    by_contra h
    apply hk
    apply hActive.2.2 k
    unfold integerRadialWindow at h
    simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), mul_comm] using h
  have shifted := (Equiv.addLeft j).tsum_eq (fun k => integerRadialWindow k p.1)
  change (∑' k : ℤ, integerRadialWindow (j+k) p.1) = ∑' k : ℤ, integerRadialWindow k p.1 at shifted
  rw [tsum_eq_sum outside, (integerRadialWindow_hasSum p.1).tsum_eq, if_neg hp0] at shifted
  change (∑ k ∈ I, radianFixedShiftBoxBlock d (normalizedLowPassCorrection χ₀ A C M₀ k) k j p) = _
  simp only [radianLowPassCorrectionBlock_factor, hThird, mul_one, ← Finset.mul_sum, ← Complex.ofReal_sum]
  rw [shifted, Complex.ofReal_one, mul_one]

end Burnett.A05
