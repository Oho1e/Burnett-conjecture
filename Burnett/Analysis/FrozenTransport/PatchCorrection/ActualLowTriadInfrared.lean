import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeA08Profile
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeOutputCutoff

set_option autoImplicit false
set_option maxHeartbeats 3400000
set_option maxRecDepth 4800

noncomputable section
namespace Burnett.V11

open MeasureTheory Matrix Burnett.A06 Burnett.A07 Burnett.P01 Burnett.V08
open Burnett.A02.FrequencySplit (E Joint radianFourier)
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight lowSlotWeight_nonzero_small)
open scoped Matrix ContDiff ComplexConjugate

theorem separated_high_norms_of_original_low (θ : ℝ → ℝ) (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hsmall : κ < 1/16) {p q : E} (hp : 1 < ‖p‖) (hq : q ≠ 0)
    (hLow : lowSlotWeight θ κ p q (-(p+q)) ≠ 0) : 8 < ‖q‖ ∧ 7 < ‖p+q‖ := by
  have small := lowSlotWeight_nonzero_small hcut hκ hsmall (add_neg_cancel (p+q)) hq hLow
  have strict := mul_lt_mul_of_pos_right hsmall (norm_pos_iff.mpr hq)
  have tri : ‖q‖ ≤ ‖p+q‖ + ‖p‖ := by
    have v := norm_sub_le (p+q) p
    rwa [add_sub_cancel_left] at v
  constructor <;> nlinarith

theorem gaugeLow_spectrum_zero (z : ProjectionSchwartzMatrix) (k : TensorSlot) (p : E) (hp : ‖p‖ ≤ 1) :
    radianFourier (Burnett.C03.projectedGaugeComplement z k.1 k.2) p = 0 := by
  rw [Burnett.C03.projectedGaugeComplement_radianFourier, gaugeProjectionInfrared_zero hp, Complex.ofReal_zero, zero_mul]

theorem physicalLow_spectrum_zero (z : ProjectionSchwartzMatrix) (k : TensorSlot) (p : E) (hp : ‖p‖ ≤ 1) :
    radianFourier (projectionFullSchwartz z k.1 k.2) p = 0 := by
  simp [projectionFullSchwartz_radianFourier, regularizedComplexGaugeProjection,
    gaugeProjectionInfrared_zero hp]

/-- Any triad kernel may retain its output regularizer in a true high-passed
low field. This equality is available for arbitrary high arguments, including
Schwartz coefficient products and their derivatives. -/
theorem actualTriad_output_inert (θ : ℝ → ℝ) (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hsmall : κ < 1/16) (b : Joint → ℂ)
    (H : E → ℂ) (hH : ∀ p, ‖p‖ ≤ 1 → radianFourier H p = 0) (u v : E → ℂ) :
    radianHighPair (fun x : Joint => (gaugeTriadCutoff θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ x.1 x.2 : ℂ) * b x) H u v =
      radianHighPair (fun x : Joint => (gaugeTriadCutoff θ gaugeCorrectionInfrared (fun _ => 1) κ x.1 x.2 : ℂ) * b x) H u v := by
  unfold radianHighPair
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  obtain ⟨p,q⟩ := x
  by_cases hP : ‖p‖ ≤ 1
  · simp [radianHighPairWeight,hH p hP]
  by_cases hQ : q = 0
  · subst q
    simp [radianHighPairWeight,gaugeTriadCutoff,gaugeCorrectionInfrared_zero 0 (by norm_num)]
  by_cases hL : lowSlotWeight θ κ p q (-(p+q)) = 0
  · simp only [radianHighPairWeight,gaugeTriadCutoff,hL,zero_mul,Complex.ofReal_zero]
  have hh := separated_high_norms_of_original_low θ hcut κ hκ hsmall (lt_of_not_ge hP) hQ hL
  simp only [radianHighPairWeight,gaugeTriadCutoff,gaugeCorrectionInfrared_one _ (show 1 ≤ ‖p+q‖ by linarith [hh.2])]

/-- The actual ordered low-gauge component of the V08 raw operator is precisely
the A08 unexpanded pairing for all high inputs and tests. -/
theorem actualGaugeA08_pair (θ : ℝ → ℝ) (hcut : ∀ t : ℝ, 1 ≤ t → θ t = 0)
    (κ : ℝ) (hκ : 0 < κ) (hsmall : κ < 1/16) (m : Fin 4 → Fin 4 → ℝ) (w : ℝ)
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {x : E | x ≠ 0}) (hOdd : ∀ x, a (-x) = -a x)
    (hHom : ∀ s : ℝ, 0 < s → ∀ x, a (s • x) = s*a x)
    (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen) (hS : ∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x)
    (k i j : TensorSlot) (H : E → ℂ) (hH : ∀ p, ‖p‖ ≤ 1 → radianFourier H p = 0) (u v : E → ℂ) :
    radianHighPair (gaugeRawEntry θ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m w a C S k i j) H u v =
      radianHighPair (originalRegularizedAngularSymbol gaugeCorrectionInfrared gaugeRatioGuard
        (gaugeTriadAngularProfile θ κ m w a C S k i j)) H u v := by
  have one : gaugeRawEntry θ gaugeCorrectionInfrared (fun _ => 1) κ m w a C S k i j =
      originalRegularizedAngularSymbol gaugeCorrectionInfrared gaugeRatioGuard (gaugeTriadAngularProfile θ κ m w a C S k i j) := by
    funext x
    simpa only [Complex.ofReal_one,one_mul] using gaugeRawEntry_eq_filtered_A08 θ gaugeCorrectionInfrared
      (fun _ => 1) κ hκ hsmall hcut (gaugeCorrectionInfrared_zero 0 (by norm_num)) m w a ha hOdd hHom C S hS k i j x
  rw [← one]
  exact actualTriad_output_inert θ hcut κ hκ hsmall _ H hH u v

end Burnett.V11
