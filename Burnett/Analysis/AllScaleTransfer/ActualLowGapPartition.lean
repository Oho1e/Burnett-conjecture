import Burnett.Analysis.AllScaleTransfer.ActualIntegerRadialPartition

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.A05

open Burnett.A02.FrequencySplit

/-- On the separated side of the actual radial partition, every active
pair has a large integer high-minus-low gap. -/
theorem integerRadialWindow_gap_of_small_ratio (cutoff : ℕ) (i j : ℤ) (p q : E)
    (hp : integerRadialWindow i p ≠ 0) (hq : integerRadialWindow j q ≠ 0)
    (hsmall : ‖p‖ ≤ ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * ‖q‖) :
    (cutoff : ℤ) ≤ j - i := by
  have lowNonzero : endpointHighProfile ((2 : ℝ)^(-i) • p) ≠ 0 := by
    rw [endpointHighProfile_eq_integerRadialWindow]
    exact_mod_cast hp
  have highNonzero : endpointHighProfile ((2 : ℝ)^(-j) • q) ≠ 0 := by
    rw [endpointHighProfile_eq_integerRadialWindow]
    exact_mod_cast hq
  have hlo := (endpointHighProfile_properties.2.2 _ lowNonzero).1
  have hhi := (endpointHighProfile_properties.2.2 _ highNonzero).2
  rw [norm_smul, Real.norm_of_nonneg (zpow_nonneg (by norm_num) _), zpow_neg, inv_mul_eq_div] at hlo hhi
  have hi_pos : 0 < (2 : ℝ)^i := by positivity
  have hj_pos : 0 < (2 : ℝ)^j := by positivity
  have step : (1/2 : ℝ) * (2 : ℝ)^i < (1/2 : ℝ) * (2 : ℝ)^(j - (cutoff : ℤ)) := by
    calc
      _ < ‖p‖ := (lt_div_iff₀ hi_pos).mp hlo
      _ ≤ ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * ‖q‖ := hsmall
      _ < ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * (2 * (2 : ℝ)^j) :=
        mul_lt_mul_of_pos_left ((div_lt_iff₀ hj_pos).mp hhi) (by positivity)
      _ = _ := by
        rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_neg, div_eq_mul_inv]
        ring
  have hs : (2 : ℝ)^i < (2 : ℝ)^(j - (cutoff : ℤ)) := by linarith only [step]
  have hidx := (zpow_lt_zpow_iff_right₀ (by norm_num : 1 < (2 : ℝ))).mp hs
  omega

/-- In the separated region, grouping the exact two-window partition by
gap leaves another partition of unity. The terms are the original windows
at low index j-s and high index j. -/
theorem integerRadialWindow_hasSum_over_large_gaps (cutoff : ℕ) (p q : E)
    (hp : p ≠ 0) (hq : q ≠ 0)
    (hsmall : ‖p‖ ≤ ((2 : ℝ)^(-(cutoff : ℤ)) / 4) * ‖q‖) :
    HasSum (fun z : {s : ℕ // cutoff ≤ s} × ℤ =>
      integerRadialWindow (z.2 - (z.1.val : ℤ)) p * integerRadialWindow z.2 q) 1 := by
  obtain ⟨P, _, hP⟩ := exists_integerRadialWindow_support_card_le_three p
  obtain ⟨Q, _, hQ⟩ := exists_integerRadialWindow_support_card_le_three q
  let F (ij : ℤ × ℤ) := integerRadialWindow ij.1 p * integerRadialWindow ij.2 q
  have hFin : Summable F := by
    apply summable_of_ne_finset_zero (s := P ×ˢ Q)
    intro z hz
    by_cases hzp : z.1 ∈ P
    · have hzq : z.2 ∉ Q := fun h => hz (Finset.mem_product.mpr ⟨hzp,h⟩)
      simp only [F, hQ z.2 hzq, mul_zero]
    · simp only [F, hP z.1 hzp, zero_mul]
  have hAll : HasSum F 1 := by
    simpa only [if_neg hp, if_neg hq, one_mul] using
      (integerRadialWindow_hasSum p).mul (integerRadialWindow_hasSum q) hFin
  let e (z : {s : ℕ // cutoff ≤ s} × ℤ) : ℤ × ℤ := (z.2 - (z.1.val : ℤ), z.2)
  have he : Function.Injective e := by
    intro x y eq
    have e1 : x.2 - (x.1.val : ℤ) = y.2 - (y.1.val : ℤ) := congrArg Prod.fst eq
    have e2 : x.2 = y.2 := congrArg (fun z : ℤ × ℤ => z.2) eq
    exact Prod.ext (Subtype.ext (by omega)) e2
  have hOutside (z : ℤ × ℤ) (hz : z ∉ Set.range e) : F z = 0 := by
    by_contra hn
    have hl : integerRadialWindow z.1 p ≠ 0 := by
      intro h
      apply hn
      simp only [F, h, zero_mul]
    have hh : integerRadialWindow z.2 q ≠ 0 := by
      intro h
      apply hn
      simp only [F, h, mul_zero]
    have hs := integerRadialWindow_gap_of_small_ratio cutoff z.1 z.2 p q hl hh hsmall
    let s := (z.2 - z.1).toNat
    have hs' : (s : ℤ) = z.2 - z.1 := Int.toNat_of_nonneg (by omega)
    have hsc : cutoff ≤ s := by omega
    apply hz
    refine ⟨(⟨s,hsc⟩,z.2), Prod.ext ?_ rfl⟩
    change z.2 - (s : ℤ) = z.1
    omega
  exact (he.hasSum_iff hOutside).mpr hAll

end Burnett.A05
