import Burnett.Analysis.AllScaleTransfer.RadianLowGapAssembly
import Burnett.Analysis.AllScaleTransfer.RadianRadialBoxGapBound

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory Metric
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  radialAnnularCutoff_nonzero thickProductCutoff thickProductCutoff_eq_one)
open scoped ContDiff ENNReal

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private theorem remove_tau_at_scale (r : ℝ) (p : E) :
    (r * tau) • (tau⁻¹ • p) = r • p := by
  rw [smul_smul, mul_assoc, mul_inv_cancel₀ tau_pos.ne', mul_one]

/-- At the original gap scales the normalized box uses exactly the two
integer annuli and the actual thick third window on the negative sum. -/
theorem radianBoxBlock_eq_integer_radial_cutoffs (s : ℕ) (j : ℤ)
    (G : BoxSpace → ℂ) (p : Joint) :
    radianBoxBlock endpointHighProfile endpointHighProfile endpointThickProfile
        ((2 : ℝ)^(-j) * ((2 : ℝ)^s * tau)) ((2 : ℝ)^(-j) * tau)
        ((2 : ℝ)^(-j) * tau) G p =
      G (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) *
        ((integerRadialWindow (j - (s : ℤ)) p.1 : ℂ) * (integerRadialWindow j p.2 : ℂ) *
          (thickProductCutoff ((2 : ℝ)^j) (-(p.1+p.2)) : ℂ)) := by
  have hlow : (2 : ℝ)^(-j) * ((2 : ℝ)^s * tau) =
      (2 : ℝ)^(-(j - (s : ℤ))) * tau := by
    rw [← mul_assoc, ← zpow_natCast, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 2
    omega
  have hd : endpointThickProfile ((2 : ℝ)^(-j) • (-(p.1+p.2))) =
      (thickProductCutoff ((2 : ℝ)^j) (-(p.1+p.2)) : ℂ) := by
    have H := (endpoint_profiles_at_radian_frequency ((2 : ℝ)^j) 0 (-(p.1+p.2))).2.2
    change endpointThickProfile ((tau * ((2 : ℝ)^j)⁻¹) • (tau⁻¹ • (-(p.1+p.2)))) = _ at H
    rw [mul_comm tau, remove_tau_at_scale] at H
    simpa only [zpow_neg] using H
  unfold radianBoxBlock
  simp only [hlow, ← smul_add, ← smul_neg, remove_tau_at_scale, hd,
    endpointHighProfile_eq_integerRadialWindow]

private theorem thirdWindow_one (j : ℤ) (p : Joint) (hp : ‖p.1‖ ≤ (1/4 : ℝ) * ‖p.2‖)
    (hq : integerRadialWindow j p.2 ≠ 0) :
    thickProductCutoff ((2 : ℝ)^j) (-(p.1+p.2)) = 1 := by
  have hr : 0 < (2 : ℝ)^j := by positivity
  have H := radialAnnularCutoff_nonzero hr hq
  have hTri := norm_add_le p.1 p.2
  have hRev : ‖p.2‖ ≤ ‖p.1+p.2‖ + ‖p.1‖ := by
    have eq : p.1 + p.2 - p.1 = p.2 := by abel
    simpa only [eq] using norm_sub_le (p.1+p.2) p.1
  refine thickProductCutoff_eq_one hr ?_ ?_ <;> rw [norm_neg] <;> linarith [H.1, H.2]

/-- The normalizing box statement is used only at the active frequencies
in the original product. This verifies equality of the two integrals on
the same tested factors, including where the original symbol vanishes. -/
theorem radianTrilinearForm_radial_box_eq_lowGap (cutoff s : ℕ)
    (m : Joint → ℂ) (G : BoxSpace → ℂ) (f g h : SchwartzMap E ℂ)
    (hSupport : ∀ p, m p ≠ 0 → ‖p.1‖ ≤ ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * ‖p.2‖)
    (hMatch : ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
      integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
      G (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = m p) :
    radianTrilinearForm (fun p => ∑' j : ℤ,
        radianBoxBlock endpointHighProfile endpointHighProfile endpointThickProfile
          ((2 : ℝ)^(-j) * ((2 : ℝ)^s * tau)) ((2 : ℝ)^(-j) * tau) ((2 : ℝ)^(-j) * tau) G p) f g h =
      radianTrilinearForm (radianLowGapSymbol m s) f g h := by
  unfold radianTrilinearForm
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  let W := radianWeight (fun _ => 1) f g h p
  change (∑' j : ℤ, radianBoxBlock _ _ _
    ((2 : ℝ)^(-j) * ((2 : ℝ)^s * tau)) ((2 : ℝ)^(-j) * tau) ((2 : ℝ)^(-j) * tau) G p) * W =
      radianLowGapSymbol m s p * W
  by_cases hw : W = 0
  · simp only [hw, mul_zero]
  apply congrArg (fun c : ℂ => c * W)
  obtain ⟨I, _, hI⟩ := exists_integerRadialWindow_support_card_le_three p.2
  have hOne (j : ℤ) (hj : j ∉ I) : radianBoxBlock endpointHighProfile endpointHighProfile endpointThickProfile
      ((2 : ℝ)^(-j) * ((2 : ℝ)^s * tau)) ((2 : ℝ)^(-j) * tau) ((2 : ℝ)^(-j) * tau) G p = 0 := by
    rw [radianBoxBlock_eq_integer_radial_cutoffs, hI j hj]
    simp only [Complex.ofReal_zero, mul_zero, zero_mul]
  have hTwo (j : ℤ) (hj : j ∉ I) : integerRadialWindow (j - (s : ℤ)) p.1 * integerRadialWindow j p.2 = 0 :=
    by rw [hI j hj, mul_zero]
  rw [tsum_eq_sum (s := I) hOne, radianLowGapSymbol, tsum_eq_sum (s := I) hTwo,
    Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [radianBoxBlock_eq_integer_radial_cutoffs]
  by_cases hlow : integerRadialWindow (j - (s : ℤ)) p.1 = 0
  · simp only [hlow, zero_mul, Complex.ofReal_zero, mul_zero]
  by_cases hhigh : integerRadialWindow j p.2 = 0
  · simp only [hhigh, mul_zero, zero_mul, Complex.ofReal_zero]
  rw [hMatch j p hw hlow hhigh]
  by_cases hm : m p = 0
  · simp only [hm, zero_mul, mul_zero]
  have hpow : (2 : ℝ)^(-(cutoff : ℤ)) ≤ 1 := by
    have HH : -(cutoff : ℤ) ≤ 0 := by omega
    simpa only [zpow_zero] using zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) HH
  have hr : ‖p.1‖ ≤ (1/4 : ℝ) * ‖p.2‖ :=
    (hSupport p hm).trans (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow (by norm_num)) (norm_nonneg _))
  rw [thirdWindow_one j p hr hhigh, Complex.ofReal_one, mul_one, Complex.ofReal_mul, mul_comm]

/-- The separated low-ratio remainder in the original Fourier form has
the summed box bound, once the normalized profile is identified on the
weighted frequency support. -/
theorem exists_radianTrilinearForm_large_gap_remainder_bound (P : ℝ) (hP : 4 < P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (cutoff : ℕ) (m : Joint → ℂ) (_hm : Measurable m) (B : ℝ), 0 ≤ B →
      (∀ p, m p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0 ∧ ‖p.1‖ ≤ ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * ‖p.2‖) →
      (∀ p, ‖m p‖ ≤ B * (‖p.1‖ / ‖p.2‖)) →
      ∀ (G : ℕ → BoxSpace → ℂ) (A : ℝ), 0 ≤ A →
      (∀ s, ContDiffOn ℝ 99 (G s) (ball (0 : BoxSpace) P)) →
      (∀ s n, n ≤ 40 → ∀ z ∈ ball (0 : BoxSpace) P,
        ‖iteratedFDeriv ℝ n (G s) z‖ ≤ A * radialGapDecay s) →
      ∀ (f g h : SchwartzMap E ℂ),
      (∀ (s : ℕ), cutoff ≤ s → ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
        integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
        G s (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = m p) →
      ‖radianTrilinearForm m f g h‖ ≤ C * A * (radialGapDecay cutoff * 2) * (triLpMass f g h 3 3 3).toReal := by
  obtain ⟨C,hC,H⟩ := exists_radianRadialBoxGap_bound P hP endpointHighProfile endpointHighProfile endpointThickProfile
    endpointHighProfile_properties.2.1 endpointHighProfile_properties.2.1
    endpointHighProfile_properties.2.2 endpointHighProfile_properties.2.2
  refine ⟨C,hC,?_⟩
  intro cutoff m hm B hB hSupport hRatio G A hA hC99 hJet f g h hMatch
  have H' := H G A hA hC99 hJet (fun s => (2 : ℝ)^s * tau) (fun _ => tau)
    (fun s => mul_pos (by positivity) tau_pos) (fun _ => tau_pos)
    (fun _ j => (2 : ℝ)^(-j) * tau) (fun _ _ => mul_pos (by positivity) tau_pos) f g h
  let T (s : {s : ℕ // cutoff ≤ s}) := radianTrilinearForm
    (fun p => ∑' j : ℤ, radianBoxBlock endpointHighProfile endpointHighProfile endpointThickProfile
      ((2 : ℝ)^(-j) * ((2 : ℝ)^s.val * tau)) ((2 : ℝ)^(-j) * tau) ((2 : ℝ)^(-j) * tau) (G s.val) p) f g h
  have hEq (s : {s : ℕ // cutoff ≤ s}) :
      T s = radianTrilinearForm (radianLowGapSymbol m s.val) f g h :=
    radianTrilinearForm_radial_box_eq_lowGap cutoff s.val m (G s.val) f g h
      (fun p hup => (hSupport p hup).2.2) (hMatch s.val s.property)
  have hsum : HasSum T (radianTrilinearForm m f g h) := by
    have eq : T = fun s => radianTrilinearForm (radianLowGapSymbol m s.val) f g h := funext hEq
    rw [eq]
    exact radianTrilinearForm_hasSum_over_large_gaps cutoff m hm B hB hSupport hRatio f g h
  rw [← hsum.tsum_eq]
  exact (H'.2 cutoff).2

end Burnett.A05
