import Burnett.Analysis.AllScaleTransfer.ActualLowGapPartition
import Burnett.Analysis.AllScaleTransfer.RadianTrilinearModeSeries
import Burnett.Analysis.AllScaleTransfer.EightDimensionalModeSummation

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier (radianTrilinearForm)
open scoped Topology

private theorem integerRadialWindow_continuous (j : ℤ) : Continuous (integerRadialWindow j) := by
  have eq : (fun ξ : E => (endpointHighProfile ((2 : ℝ)^(-j) • ξ)).re) = integerRadialWindow j := by
    funext ξ
    rw [endpointHighProfile_eq_integerRadialWindow, Complex.ofReal_re]
  rw [← eq]
  exact Complex.continuous_re.comp (endpointHighProfile.continuous.comp (continuous_const.smul continuous_id))

private theorem norm_integerRadialWindow_le (j : ℤ) (ξ : E) :
    ‖integerRadialWindow j ξ‖ ≤ SchwartzMap.seminorm ℝ 0 0 endpointHighProfile := by
  have h := endpointHighProfile.norm_le_seminorm ℝ ((2 : ℝ)^(-j) • ξ)
  rw [endpointHighProfile_eq_integerRadialWindow, Complex.norm_real] at h
  exact h

private theorem active_window_ratio_le (s : ℕ) (j : ℤ) (p q : E)
    (hp : integerRadialWindow (j - (s : ℤ)) p ≠ 0) (hq : integerRadialWindow j q ≠ 0) :
    ‖p‖ / ‖q‖ ≤ 4 * radialGapDecay s := by
  let i := j - (s : ℤ)
  have hpn : endpointHighProfile ((2 : ℝ)^(-i) • p) ≠ 0 := by
    rw [endpointHighProfile_eq_integerRadialWindow]
    exact_mod_cast hp
  have hqn : endpointHighProfile ((2 : ℝ)^(-j) • q) ≠ 0 := by
    rw [endpointHighProfile_eq_integerRadialWindow]
    exact_mod_cast hq
  have hup := (endpointHighProfile_properties.2.2 _ hpn).2
  have hlo := (endpointHighProfile_properties.2.2 _ hqn).1
  rw [norm_smul, Real.norm_of_nonneg (zpow_nonneg (by norm_num) _), zpow_neg, inv_mul_eq_div] at hup hlo
  have hi : 0 < (2 : ℝ)^i := by positivity
  have hj : 0 < (2 : ℝ)^j := by positivity
  have hhi := (div_lt_iff₀ hi).mp hup
  have hlow := (lt_div_iff₀ hj).mp hlo
  have hqpos : 0 < ‖q‖ := (by positivity : 0 < (1/2 : ℝ) * (2 : ℝ)^j).trans hlow
  have e : (2 : ℝ)^i = (2 : ℝ)^j * radialGapDecay s := by
    unfold i radialGapDecay
    rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_natCast, div_pow, one_pow, one_div, div_eq_mul_inv]
  apply (div_le_iff₀ hqpos).mpr
  calc
    _ ≤ 2 * (2 : ℝ)^i := hhi.le
    _ = (4 * radialGapDecay s) * ((1/2) * (2 : ℝ)^j) := by rw [e]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow.le (by unfold radialGapDecay; positivity)

/-- The genuine low/high symbol restricted to the separated tail of the
radial partition. The axes have zero symbol, and the original paired
frequencies are unchanged in each Fourier integral. -/
def radianLowGapSymbol (m : Joint → ℂ) (s : ℕ) (p : Joint) : ℂ :=
  ((∑' j : ℤ, integerRadialWindow (j - (s : ℤ)) p.1 * integerRadialWindow j p.2 : ℝ) : ℂ) * m p

/-- On the strongly separated region, summing the actual Fourier forms
over all gaps recovers the original form. A first-order ratio bound gives
an integrable geometric majorant for the same symbol pieces. -/
theorem radianTrilinearForm_hasSum_over_large_gaps
    (cutoff : ℕ) (m : Joint → ℂ) (hm : Measurable m) (B : ℝ) (hB : 0 ≤ B)
    (hSupport : ∀ p, m p ≠ 0 → p.1 ≠ 0 ∧ p.2 ≠ 0 ∧
      ‖p.1‖ ≤ ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * ‖p.2‖)
    (hRatio : ∀ p, ‖m p‖ ≤ B * (‖p.1‖ / ‖p.2‖))
    (f g h : SchwartzMap E ℂ) :
    HasSum (fun s : {s : ℕ // cutoff ≤ s} => radianTrilinearForm (radianLowGapSymbol m s.val) f g h)
      (radianTrilinearForm m f g h) := by
  let W (s : ℕ) (j : ℤ) (p : Joint) := integerRadialWindow (j - (s : ℤ)) p.1 * integerRadialWindow j p.2
  let L := SchwartzMap.seminorm ℝ 0 0 endpointHighProfile
  have hL : 0 ≤ L := by unfold L; positivity
  have hLoc (p : Joint) : ∃ I : Finset ℤ, I.card ≤ 3 ∧ ∀ j ∉ I, ∀ s, W s j p = 0 := by
    obtain ⟨I,hI,hzero⟩ := exists_integerRadialWindow_support_card_le_three p.2
    exact ⟨I,hI,fun j hj s => by simp only [W,hzero j hj,mul_zero]⟩
  have hfinite (s : ℕ) (p : Joint) : Summable (fun j => W s j p) := by
    obtain ⟨I,_,hzero⟩ := hLoc p
    exact summable_of_ne_finset_zero (fun j hj => hzero j hj s)
  have hwmeas (s : ℕ) : Measurable (fun p => ∑' j, W s j p) := by
    apply measurable_of_tendsto_metrizable' (atTop : Filter (Finset ℤ)) (f := fun I p => ∑ j ∈ I, W s j p)
    · intro I
      exact (continuous_finset_sum I (fun j _ => ((integerRadialWindow_continuous _).comp continuous_fst).mul
        ((integerRadialWindow_continuous _).comp continuous_snd))).measurable
    · rw [tendsto_pi_nhds]
      intro p
      have hs : HasSum (fun j => W s j p) (∑' j, W s j p) := (hfinite s p).hasSum
      exact hs
  let S := {s : ℕ // cutoff ≤ s}
  let F (s : S) := radianLowGapSymbol m s.val
  let C := (L * L) * (4 * B)
  have hC : 0 ≤ C := by unfold C; positivity
  have hfMeas (s : S) : AEStronglyMeasurable (F s) volume :=
    ((Complex.continuous_ofReal.measurable.comp (hwmeas s.val)).mul hm).aestronglyMeasurable
  have hTerm (s : S) (j : ℤ) (p : Joint) : ‖(W s.val j p : ℂ) * m p‖ ≤ C * radialGapDecay s.val := by
    by_cases hp : integerRadialWindow (j - (s.val : ℤ)) p.1 = 0
    · have hh : 0 ≤ C * radialGapDecay s.val := by unfold radialGapDecay; positivity
      simpa only [W, hp, zero_mul, Complex.ofReal_zero, norm_zero] using hh
    by_cases hq : integerRadialWindow j p.2 = 0
    · have hh : 0 ≤ C * radialGapDecay s.val := by unfold radialGapDecay; positivity
      simpa only [W, hq, mul_zero, Complex.ofReal_zero, zero_mul, norm_zero] using hh
    have hM : ‖m p‖ ≤ B * (4 * radialGapDecay s.val) :=
      (hRatio p).trans (mul_le_mul_of_nonneg_left (active_window_ratio_le s.val j p.1 p.2 hp hq) hB)
    simp only [W, norm_mul, Complex.norm_real]
    refine (mul_le_mul (mul_le_mul (norm_integerRadialWindow_le _ _) (norm_integerRadialWindow_le _ _)
      (norm_nonneg _) hL) hM (norm_nonneg _) (mul_nonneg hL hL)).trans_eq ?_
    unfold C
    ring
  have hF (s : S) (p : Joint) : ‖F s p‖ ≤ (3 * C) * radialGapDecay s.val := by
    obtain ⟨I,hI,hzero⟩ := hLoc p
    have hEq : F s p = ∑ j ∈ I, (W s.val j p : ℂ) * m p := by
      change ((∑' j, W s.val j p : ℝ) : ℂ) * m p = _
      rw [tsum_eq_sum (s := I) (fun j hj => hzero j hj s.val), Complex.ofReal_sum, Finset.sum_mul]
    rw [hEq]
    calc
      _ ≤ ∑ j ∈ I, C * radialGapDecay s.val := norm_sum_le_of_le _ (fun j _ => hTerm s j p)
      _ = (I.card : ℝ) * (C * radialGapDecay s.val) := by simp
      _ ≤ 3 * (C * radialGapDecay s.val) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hI) (by unfold radialGapDecay; positivity)
      _ = _ := by ring
  have hPoint : ∀ᵐ p ∂(volume : Measure Joint), HasSum (fun s : S => F s p) (m p) := by
    apply Eventually.of_forall
    intro p
    by_cases hp : m p = 0
    · simp only [F, radianLowGapSymbol, hp, mul_zero]
      exact hasSum_zero
    obtain ⟨hp1,hp2,hr⟩ := hSupport p hp
    have hpair : HasSum (fun x : S × ℤ => W x.1.val x.2 p) 1 :=
      integerRadialWindow_hasSum_over_large_gaps cutoff p.1 p.2 hp1 hp2 hr
    have hs : HasSum (fun s : S => ∑' j, W s.val j p) 1 :=
      hpair.prod_fiberwise (fun s => (hfinite s.val p).hasSum)
    have hcs := (Complex.hasSum_ofReal.mpr hs).mul_right (m p)
    simpa only [F, radianLowGapSymbol, Complex.ofReal_one, one_mul] using hcs
  exact radianTrilinearForm_hasSum_of_symbol_expansion F m _
    hfMeas ((hasSum_radialGapDecay cutoff).summable.mul_left (3*C)) hF hPoint f g h

end Burnett.A05
