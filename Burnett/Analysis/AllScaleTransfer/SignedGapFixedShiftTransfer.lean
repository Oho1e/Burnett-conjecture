import Burnett.Analysis.AllScaleTransfer.SignedRadianGapSeries
import Burnett.Analysis.AllScaleTransfer.FixedShiftRadianBoxTransfer

set_option autoImplicit false

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm)

/-- A transition term in the signed split is the actual fixed-shift box
form when its normalized symbol and third window reproduce the original
symbol on the active windows of the original Fourier integrand. -/
theorem radianTrilinearForm_signedGap_eq_fixedShiftBoxForm
    (m : Joint → ℂ) (d : SchwartzMap E ℂ) (G : BoxSpace → ℂ)
    (k : ℤ) (f g h : SchwartzMap E ℂ)
    (hMatch : ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
      integerRadialWindow (j+k) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
      G (joinedInputs ((2 : ℝ)^(-(j+k)) • p.1) ((2 : ℝ)^(-j) • p.2)) *
        d ((2 : ℝ)^(-j) • (-(p.1+p.2))) = m p) :
    radianTrilinearForm (radianSignedGapSymbol m k) f g h =
      radianFixedShiftBoxForm d G k f g h := by
  unfold radianFixedShiftBoxForm radianTrilinearForm
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  let W := radianWeight (fun _ => 1) f g h p
  change radianSignedGapSymbol m k p * W =
    (∑' j : ℤ, radianFixedShiftBoxBlock d G k j p) * W
  by_cases hw : W = 0
  · simp only [hw, mul_zero]
  apply congrArg (fun z : ℂ => z * W)
  obtain ⟨I, _, hI⟩ := exists_integerRadialWindow_support_card_le_three p.2
  have hMask (j : ℤ) (hj : j ∉ I) : integerRadialWindow (j+k) p.1 *
      integerRadialWindow j p.2 = 0 := by rw [hI j hj, mul_zero]
  have hBlock (j : ℤ) (hj : j ∉ I) : radianFixedShiftBoxBlock d G k j p = 0 := by
    simp only [radianFixedShiftBoxBlock, hI j hj, Complex.ofReal_zero, mul_zero, zero_mul]
  rw [radianSignedGapSymbol, tsum_eq_sum (s := I) hMask, tsum_eq_sum (s := I) hBlock,
    Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  unfold radianFixedShiftBoxBlock
  by_cases hLow : integerRadialWindow (j+k) p.1 = 0
  · simp only [hLow, Complex.ofReal_zero, mul_zero, zero_mul]
  by_cases hHigh : integerRadialWindow j p.2 = 0
  · simp only [hHigh, Complex.ofReal_zero, mul_zero, zero_mul]
  rw [← hMatch j p hw hLow hHigh, Complex.ofReal_mul]
  ring

end Burnett.A05
