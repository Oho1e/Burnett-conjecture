import Burnett.Analysis.AllScaleTransfer.RadianBoxGapOnSource

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.A05

open Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier (radianTrilinearForm radialAnnularCutoff_nonzero)
open scoped ContDiff ENNReal

private theorem active_pair_ratio_of_gap {s : ℕ} (hs : 4 ≤ s) (j : ℤ) (p : Joint)
    (hlo : integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0) (hhi : integerRadialWindow j p.2 ≠ 0) :
    ‖p.1‖ ≤ (1 / 4 : ℝ) * ‖p.2‖ := by
  have lo := (radialAnnularCutoff_nonzero (by positivity : 0 < (2 : ℝ)^(j - (s : ℤ))) hlo).2
  have hi := (radialAnnularCutoff_nonzero (by positivity : 0 < (2 : ℝ)^j) hhi).1
  have hexp : j - (s : ℤ) ≤ j - 4 := by omega
  have hpow := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hexp
  have heq : (2 : ℝ)^(j - 4) = (2 : ℝ)^j / 16 := by
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0)]
    norm_num
  rw [heq] at hpow
  linarith only [lo, hi, hpow]

/-- At a large integer gap the exact thick third window is inserted on
every active pair. The original symbol may be nonzero at other gaps. -/
theorem radianTrilinearForm_radial_box_eq_dyadic_gap {s : ℕ} (hs : 4 ≤ s)
    (m : Joint → ℂ) (G : BoxSpace → ℂ) (f g h : SchwartzMap E ℂ)
    (hMatch : ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
      integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
      G (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = m p) :
    radianTrilinearForm (fun p => ∑' j : ℤ,
        radianBoxBlock endpointHighProfile endpointHighProfile endpointThickProfile
          ((2 : ℝ)^(-j) * ((2 : ℝ)^s * tau)) ((2 : ℝ)^(-j) * tau) ((2 : ℝ)^(-j) * tau) G p) f g h =
      radianTrilinearForm (radianLowGapSymbol m s) f g h := by
  let M (p : Joint) := if ‖p.1‖ ≤ (1 / 4 : ℝ) * ‖p.2‖ then m p else 0
  have hM (p : Joint) (hp : M p ≠ 0) :
      ‖p.1‖ ≤ ((2 : ℝ)^(-(0 : ℤ)) / 4) * ‖p.2‖ := by
    simp only [neg_zero, zpow_zero]
    by_contra hn
    exact hp (if_neg hn)
  have hMatchM (j : ℤ) (p : Joint) (hw : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hl : integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0) (hh : integerRadialWindow j p.2 ≠ 0) :
      G (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = M p :=
    (hMatch j p hw hl hh).trans (if_pos (active_pair_ratio_of_gap hs j p hl hh)).symm
  have he : radianLowGapSymbol M s = radianLowGapSymbol m s := by
    funext p
    by_cases hp : ‖p.1‖ ≤ (1 / 4 : ℝ) * ‖p.2‖
    · simp only [radianLowGapSymbol, M, if_pos hp]
    have hz (j : ℤ) : integerRadialWindow (j - (s : ℤ)) p.1 * integerRadialWindow j p.2 = 0 := by
      by_contra h
      exact hp (active_pair_ratio_of_gap hs j p
        (fun hl => h (by rw [hl, zero_mul])) (fun hh => h (by rw [hh, mul_zero])))
    simp only [radianLowGapSymbol, hz, tsum_zero, Complex.ofReal_zero, zero_mul]
  rw [← he]
  exact radianTrilinearForm_radial_box_eq_lowGap 0 s M G f g h hM hMatchM

/-- The actual tail selected by the integer radial partition satisfies
the box bound with the geometric sum in the original trilinear form. -/
theorem exists_radianTrilinearForm_dyadic_remainder_tail_bound (P : ℝ) (hP : 4 < P) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (cutoff : ℕ), 4 ≤ cutoff →
      ∀ (m : Joint → ℂ) (G : ℕ → BoxSpace → ℂ) (A : ℝ), 0 ≤ A →
      (∀ s, ContDiffOn ℝ 99 (G s) (ball (0 : BoxSpace) P)) →
      (∀ s n, n ≤ 40 → ∀ z ∈ ball (0 : BoxSpace) P,
        ‖iteratedFDeriv ℝ n (G s) z‖ ≤ A * radialGapDecay s) →
      ∀ (f g h : SchwartzMap E ℂ),
      (∀ (s : ℕ), cutoff ≤ s → ∀ (j : ℤ) (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
        integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0 → integerRadialWindow j p.2 ≠ 0 →
        G s (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = m p) →
      let T (s : {s : ℕ // cutoff ≤ s}) := radianTrilinearForm (radianLowGapSymbol m s.val) f g h
      let M := (triLpMass f g h 3 3 3).toReal
      (∀ s, ‖T s‖ ≤ C * A * radialGapDecay s.val * M) ∧
      Summable (fun s => ‖T s‖) ∧ ‖∑' s, T s‖ ≤ C * A * (radialGapDecay cutoff * 2) * M := by
  obtain ⟨C,hC,H⟩ := exists_radianRadialBoxGap_bound P hP endpointHighProfile endpointHighProfile endpointThickProfile
    endpointHighProfile_properties.2.1 endpointHighProfile_properties.2.1
    endpointHighProfile_properties.2.2 endpointHighProfile_properties.2.2
  refine ⟨C,hC,?_⟩
  intro cutoff hcut m G A hA hC99 hJet f g h hMatch T M
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have H' := H G A hA hC99 hJet (fun s => (2 : ℝ)^s * tau) (fun _ => tau)
    (fun s => mul_pos (by positivity) hτ) (fun _ => hτ)
    (fun _ j => (2 : ℝ)^(-j) * tau) (fun _ _ => mul_pos (by positivity) hτ) f g h
  let F (s : ℕ) := radianTrilinearForm (fun p => ∑' j : ℤ,
    radianBoxBlock endpointHighProfile endpointHighProfile endpointThickProfile
      ((2 : ℝ)^(-j) * ((2 : ℝ)^s * tau)) ((2 : ℝ)^(-j) * tau) ((2 : ℝ)^(-j) * tau) (G s) p) f g h
  have hEq (s : {s : ℕ // cutoff ≤ s}) : F s.val = T s :=
    radianTrilinearForm_radial_box_eq_dyadic_gap (hcut.trans s.property) m (G s.val) f g h
      (hMatch s.val s.property)
  have hEqFun : (fun s : {s : ℕ // cutoff ≤ s} => F s.val) = T := funext hEq
  refine ⟨fun s => (congrArg norm (hEq s).symm).trans_le (H'.1 s.val), ?_⟩
  have hTail := H'.2 cutoff
  change Summable (fun s : {s : ℕ // cutoff ≤ s} => ‖F s.val‖) ∧
    ‖∑' s : {s : ℕ // cutoff ≤ s}, F s.val‖ ≤ C * A * (radialGapDecay cutoff * 2) * M at hTail
  rw [← hEqFun]
  exact hTail

end Burnett.A05
