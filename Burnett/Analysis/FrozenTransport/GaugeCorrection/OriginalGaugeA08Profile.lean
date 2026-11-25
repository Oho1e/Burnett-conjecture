import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeRawOrder
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalMixedWeakEnergy

set_option autoImplicit false
set_option maxHeartbeats 3900000
set_option maxRecDepth 4500

noncomputable section
namespace Burnett.V08

open Set Metric MeasureTheory Matrix Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01
open Burnett.A02.FrequencySplit (E Joint)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight lowSlotWeight_nonzero_small)
open scoped ContDiff Matrix

/-- Smooth sizing cutoff for the squared ratio. It equals one on the support
of the full triad mask when `0 < κ < 1/16`. -/
def gaugeRatioGuard (s : ℝ) : ℝ := 1 - gaugeProjectionInfrared (64*s)

theorem gaugeRatioGuard_smooth : ContDiff ℝ ∞ gaugeRatioGuard :=
  contDiff_const.sub (gaugeProjectionInfrared_contDiff.comp (contDiff_const.mul contDiff_id))

theorem gaugeRatioGuard_vanishes {s : ℝ} (h : (1/4 : ℝ)^2 ≤ s) : gaugeRatioGuard s = 0 := by
  rw [gaugeRatioGuard, gaugeProjectionInfrared_one (show 2 ≤ 64*s by nlinarith), sub_self]

def gaugeTriadAngularProfile (θ : ℝ → ℝ) (κ : ℝ) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (k i j : TensorSlot) (x : Joint × E) : ℂ :=
  (lowSlotWeight θ κ x.1.1 x.1.2 (-(x.1.1 + x.1.2)) : ℂ) *
    lowGaugeAngularExpansionProfile m w a (gaugeEntryBasis k) C S i j x

private theorem lowMask_scale (θ : ℝ → ℝ) (κ : ℝ) (p q : E) (t : ℝ) (ht : 0 < t) :
    lowSlotWeight θ κ (t • p) (t • q) (-(t • p+t • q)) = lowSlotWeight θ κ p q (-(p+q)) := by
  simp only [lowSlotWeight, ← smul_add, norm_neg, norm_smul, Real.norm_of_nonneg ht.le, mul_pow]
  apply congrArg θ
  rw [← mul_add, mul_left_comm (κ^2) (t^2), mul_div_mul_left _ _ (pow_ne_zero 2 ht.ne')]

/-- The A08 unexpanded angular symbol exactly recovers the paper's raw entries,
including the second high cutoff which multiplies at the output frequency. -/
theorem gaugeRawEntry_eq_filtered_A08 (θ hi ho : ℝ → ℝ) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1/16)
    (hCut : ∀ t : ℝ, 1 ≤ t → θ t = 0) (hHi0 : hi 0 = 0) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (hOdd : ∀ x, a (-x) = -a x)
    (hHom : ∀ t : ℝ, 0 < t → ∀ x, a (t • x) = t * a x)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (hS : ∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x)
    (k i j : TensorSlot) (x : Joint) :
    gaugeRawEntry θ hi ho κ m w a C S k i j x = (ho ‖x.2+x.1‖ : ℂ) *
      originalRegularizedAngularSymbol hi gaugeRatioGuard (gaugeTriadAngularProfile θ κ m w a C S k i j) x := by
  obtain ⟨p,q⟩ := x
  by_cases hq : q = 0
  · subst q
    simp [gaugeRawEntry,gaugeTriadCutoff,hHi0,originalRegularizedAngularSymbol,regularizedLowCartesianSymbol,
      lowCartesianSymbol]
  have hq' := norm_pos_iff.mpr hq
  let hdir := ‖q‖⁻¹ • q
  let lo := ‖p‖⁻¹ • p
  let ratio := ‖q‖⁻¹ • p
  let F := lowGaugeAngularExpansionProfile m w a (gaugeEntryBasis k) C S i j
  let L := lowSlotWeight θ κ p q (-(p+q))
  have scale : lowSlotWeight θ κ ratio hdir (-(ratio+hdir)) = L :=
    lowMask_scale θ κ p q _ (inv_pos.mpr hq')
  change (↑(L * hi ‖q‖ * ho ‖p+q‖) : ℂ) * _ = ↑(ho ‖q+p‖) *
    ((hi ‖q‖) • (‖q‖ • (gaugeRatioGuard (‖ratio‖^2) •
      ((lowSlotWeight θ κ ratio hdir (-(ratio+hdir)) : ℂ) * F ((ratio,hdir),lo)))))
  rw [scale, add_comm q p]
  simp only [Complex.real_smul, Complex.ofReal_mul]
  by_cases hLow : L = 0
  · simp [hLow]
  have hSmallLow := lowSlotWeight_nonzero_small hCut hκ hSmall (add_neg_cancel (p+q)) hq hLow
  have hRatEq : ‖ratio‖ = ‖p‖ / ‖q‖ := by
    simp [ratio,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hq'.le), div_eq_inv_mul]
  have hRat : ‖ratio‖ < 1/8 := by
    rw [hRatEq,div_lt_iff₀ hq']
    nlinarith [mul_lt_mul_of_pos_right hSmall hq']
  have hOne : gaugeRatioGuard (‖ratio‖^2) = 1 := by
    rw [gaugeRatioGuard, gaugeProjectionInfrared_zero (show 64*‖ratio‖^2 ≤ 1 by nlinarith [sq_nonneg ‖ratio‖, mul_self_lt_mul_self (norm_nonneg ratio) hRat]), sub_zero]
  rw [hOne, Complex.ofReal_one, one_mul]
  by_cases hp : p = 0
  · subst p
    simp [F, lo, lowGaugeAngularExpansionProfile, lowGaugeJointProfile, lowGaugeNormalizedHighDifference,
      lowGaugeHighDifference, normalizedGaugePotential_apply, lowGaugeCorrectionCoefficient, gaugeEntryPotential]
  have hp' := norm_pos_iff.mpr hp
  have hs : ratio = (‖p‖/‖q‖) • lo := by
    simp [ratio,lo,smul_smul,div_eq_mul_inv,mul_right_comm _ ‖q‖⁻¹, hp'.ne']
  have v := gaugeBasisCoefficient_normalized (gaugeEntryBasis k) m w a ha hOdd hHom C S hS lo ratio hdir
    ‖p‖ ‖q‖ hp' hq' (norm_smul_inv_norm (𝕜 := ℝ) hp) (norm_smul_inv_norm (𝕜 := ℝ) hq)
    (hRat.trans (by norm_num)) hs i j
  have eq : lowGaugeCorrectionCoefficient m w a (gaugeEntryPotential (gaugeEntryBasis k)) C S p q i j =
      (‖q‖ : ℂ) * F ((ratio,hdir),lo) := by
    simpa only [lo,hdir,smul_smul, mul_inv_cancel₀ hp'.ne', mul_inv_cancel₀ hq'.ne', one_smul,
      F,lowGaugeAngularExpansionProfile, lowGaugeJointProfile,mul_assoc] using v
  rw [eq]
  ring

end Burnett.V08
