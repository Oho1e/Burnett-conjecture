import Burnett.Analysis.AllScaleTransfer.LowEndpointWindows

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.A05

open Filter Finset
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open scoped BigOperators

/-- The actual windows `Δ_j` with the integer index in the radian frequency. -/
def integerRadialWindow (j : ℤ) (ξ : E) : ℝ := radialAnnularCutoff ((2 : ℝ)^j) ξ

theorem endpointHighProfile_eq_integerRadialWindow (j : ℤ) (ξ : E) :
    endpointHighProfile ((2 : ℝ)^(-j) • ξ) = (integerRadialWindow j ξ : ℂ) := by
  rw [endpointHighProfile_properties.1, mikhlinWindow]
  unfold integerRadialWindow radialAnnularCutoff radialLowCutoff
  have hBall : mikhlinBall = radialBallBump := rfl
  rw [hBall, zpow_neg, smul_smul, inv_div, div_eq_mul_inv]

@[simp]
theorem integerRadialWindow_zero (j : ℤ) : integerRadialWindow j (0 : E) = 0 := by
  simp [integerRadialWindow, radialAnnularCutoff, radialLowCutoff]

/-- The auxiliary annular-overlap estimate used in the radial series.
The proof is the previously checked `annulus_indices` argument. -/
theorem exists_integer_radial_annulus_indices (r : ℝ) :
    ∃ J : Finset ℤ, J.card ≤ 3 ∧
      ∀ j : ℤ, 1/2 < (2 : ℝ)^(-j) * r → (2 : ℝ)^(-j) * r < 2 → j ∈ J := by
  by_cases h : ∃ j : ℤ, 1/2 < (2 : ℝ)^(-j) * r ∧ (2 : ℝ)^(-j) * r < 2
  · obtain ⟨k, hk⟩ := h
    have hr : 0 ≤ r := by
      by_contra! hn
      have hneg := mul_nonpos_of_nonneg_of_nonpos
        (zpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) (-k)) hn.le
      linarith only [hneg, hk.1]
    have close (i j : ℤ) (hi : (2 : ℝ)^(-i) * r < 2)
        (hj : 1/2 < (2 : ℝ)^(-j) * r) : j ≤ i + 1 := by
      by_contra! hfar
      have hexp : -j + 2 ≤ -i := by omega
      have hpow := zpow_le_zpow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) hexp
      have hpow' : (4 : ℝ) * 2^(-j) ≤ 2^(-i) := by
        calc
          _ = (2 : ℝ)^(-j) * 2^(2 : ℤ) := by norm_num [mul_comm]
          _ = (2 : ℝ)^(-j + 2) := (zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0) _ _).symm
          _ ≤ _ := hpow
      have hm := mul_le_mul_of_nonneg_right hpow' hr
      nlinarith only [hm, hi, hj]
    refine ⟨Finset.Icc (k - 1) (k + 1), ?_, ?_⟩
    · rw [Int.card_Icc]
      omega
    · intro j hj₁ hj₂
      refine Finset.mem_Icc.mpr ⟨?_, close k j hk.2 hj₁⟩
      have := close j k hj₂ hk.1
      omega
  · exact ⟨∅, by simp, fun j h₁ h₂ => (h ⟨j, h₁, h₂⟩).elim⟩

/-- At most three integer windows can be active at any fixed frequency. -/
theorem exists_integerRadialWindow_support_card_le_three (ξ : E) :
    ∃ J : Finset ℤ, J.card ≤ 3 ∧
      ∀ j : ℤ, j ∉ J → integerRadialWindow j ξ = 0 := by
  obtain ⟨J, hJ, hI⟩ := exists_integer_radial_annulus_indices ‖ξ‖
  refine ⟨J, hJ, fun j hj => ?_⟩
  by_contra hWin
  have hr : 0 < (2 : ℝ)^j := by positivity
  have hAnn := radialAnnularCutoff_nonzero hr hWin
  apply hj
  apply hI j <;> rw [zpow_neg, inv_mul_eq_div]
  · exact (lt_div_iff₀ hr).2 (by linarith only [hAnn.1])
  · exact (div_lt_iff₀ hr).2 hAnn.2

/-- The consecutive integer block is exactly the difference between its two low-pass endpoints. -/
theorem integerRadialWindow_block_sum (j : ℤ) (length : ℕ) (ξ : E) :
    (∑ i ∈ Finset.Icc (j + 1 - (length : ℤ)) j, integerRadialWindow i ξ) =
      radialLowCutoff ((2 : ℝ)^j) ξ - radialLowCutoff ((2 : ℝ)^(j - (length : ℤ))) ξ := by
  have ha (y : E) : endpointHighProfile y = ((mikhlinWindow y * (1 : ℝ) : ℝ) : ℂ) := by
    simpa only [mul_one] using endpointHighProfile_properties.1 y
  have hBall : mikhlinBall = radialBallBump := rfl
  have hTwo : (2 : ℝ) ≠ 0 := by norm_num
  have scaled (k : ℕ) : (2 : ℝ)^k * (2 : ℝ)^(-j) = (2 : ℝ)^(-(j - (k : ℤ))) := by
    rw [neg_sub, zpow_sub₀ hTwo, zpow_natCast, zpow_neg, div_eq_mul_inv]
  have hTel := mikhlin_telescope (fun _ => (1 : ℝ)) (fun _ _ _ => rfl)
    endpointHighProfile ha ((2 : ℝ)^(-j)) (by positivity) ξ length
  simp only [scaled, endpointHighProfile_eq_integerRadialWindow, Complex.ofReal_one, mul_one] at hTel
  have reindex :
      (∑ k ∈ Finset.range length, (integerRadialWindow (j - (k : ℤ)) ξ : ℂ)) =
        ∑ i ∈ Finset.Icc (j + 1 - (length : ℤ)) j, (integerRadialWindow i ξ : ℂ) := by
    refine Finset.sum_bij (fun k _ => j - (k : ℤ)) ?_ ?_ ?_ ?_
    · intro k hk
      have hk' := Finset.mem_range.mp hk
      change j - (k : ℤ) ∈ Finset.Icc (j + 1 - (length : ℤ)) j
      exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
    · intro k _ l _ h
      change j - (k : ℤ) = j - (l : ℤ) at h
      omega
    · intro i hi
      obtain ⟨hlo, hhi⟩ := Finset.mem_Icc.mp hi
      refine ⟨(j-i).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      change j - ((j-i).toNat : ℤ) = i
      omega
    · intro k hk
      rfl
  rw [reindex, ← Complex.ofReal_sum, hBall] at hTel
  apply Complex.ofReal_injective
  simpa only [radialLowCutoff, zpow_neg] using hTel

/-- The closed symmetric integer truncation, including both boundary indices. -/
theorem integerRadialWindow_symmetric_sum (N : ℕ) (ξ : E) :
    (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), integerRadialWindow j ξ) =
      radialLowCutoff ((2 : ℝ)^N) ξ - radialLowCutoff (((2 : ℝ)^(N+1))⁻¹) ξ := by
  have hlo : (N : ℤ) + 1 - ((N+N+1 : ℕ) : ℤ) = -(N : ℤ) := by omega
  have hLast : (N : ℤ) - ((N+N+1 : ℕ) : ℤ) = -((N+1 : ℕ) : ℤ) := by omega
  simpa only [hlo, hLast, zpow_neg, zpow_natCast] using
    integerRadialWindow_block_sum (N : ℤ) (N+N+1) ξ

private theorem eventually_radial_size (ξ : E) (hξ : ξ ≠ 0) :
    ∀ᶠ N : ℕ in atTop, ‖ξ‖ ≤ (2 : ℝ)^N ∧ ((2 : ℝ)^N)⁻¹ ≤ ‖ξ‖ := by
  have hNorm := norm_pos_iff.mpr hξ
  have hBig := (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually
    (eventually_ge_atTop (max ‖ξ‖ (1 / ‖ξ‖)))
  filter_upwards [hBig] with N hN
  refine ⟨(le_max_left _ _).trans hN, ?_⟩
  rw [← one_div]
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)).mpr
  have hSmall := (div_le_iff₀ hNorm).mp ((le_max_right _ _).trans hN)
  simpa only [mul_comm] using hSmall

private theorem integerRadialWindow_nonzero_mem_symmetric (ξ : E) {N : ℕ}
    (hLarge : ‖ξ‖ ≤ (2 : ℝ)^N) (hSmall : ((2 : ℝ)^N)⁻¹ ≤ ‖ξ‖) {j : ℤ}
    (h : integerRadialWindow j ξ ≠ 0) : j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
  have hOneTwo : (1 : ℝ) ≤ 2 := by norm_num
  have hTwo : (2 : ℝ) ≠ 0 := by norm_num
  have hAnn := radialAnnularCutoff_nonzero (by positivity) h
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · by_contra! hFar
    have hExp : j + 1 ≤ -(N : ℤ) := by omega
    have hPow := zpow_le_zpow_right₀ hOneTwo hExp
    have hr : 2 * (2 : ℝ)^j ≤ ((2 : ℝ)^N)⁻¹ := by
      simpa only [zpow_add₀ hTwo, zpow_one, zpow_neg, zpow_natCast, mul_comm] using hPow
    exact (not_lt_of_ge (hr.trans hSmall)) hAnn.2
  · by_contra! hFar
    have hExp : (N : ℤ) ≤ j - 1 := by omega
    have hPow := zpow_le_zpow_right₀ hOneTwo hExp
    have hr : (2 : ℝ)^N ≤ (2 : ℝ)^j / 2 := by
      simpa only [zpow_sub₀ hTwo, zpow_one, zpow_natCast] using hPow
    exact (not_lt_of_ge (hLarge.trans hr)) hAnn.1

/-- Each fixed frequency has finitely many nonzero integer windows, and every
sufficiently large symmetric truncation already gives the full value. -/
theorem integerRadialWindow_eventually_symmetric (ξ : E) :
    ∀ᶠ N : ℕ in atTop,
      (∀ j : ℤ, j ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) → integerRadialWindow j ξ = 0) ∧
      (∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), integerRadialWindow j ξ) = if ξ = 0 then 0 else 1 := by
  classical
  by_cases hξ : ξ = 0
  · subst ξ
    exact Eventually.of_forall (fun _ => by simp)
  filter_upwards [eventually_radial_size ξ hξ] with N hN
  refine ⟨fun j hj => ?_, ?_⟩
  · by_contra hn
    exact hj (integerRadialWindow_nonzero_mem_symmetric ξ hN.1 hN.2 hn)
  · have hEq : 2 * ((2 : ℝ)^(N+1))⁻¹ = ((2 : ℝ)^N)⁻¹ := by
      rw [pow_succ, mul_inv_rev, ← mul_assoc]
      norm_num
    rw [integerRadialWindow_symmetric_sum, if_neg hξ,
      radialLowCutoff_eq_one (by positivity) hN.1,
      radialLowCutoff_eq_zero (by positivity) (hEq.trans_le hN.2), sub_zero]

/-- Pointwise unit decomposition off the zero frequency and zero on the axis. -/
theorem integerRadialWindow_hasSum (ξ : E) :
    HasSum (fun j : ℤ => integerRadialWindow j ξ) (if ξ = 0 then 0 else 1) := by
  classical
  obtain ⟨N, hOutside, hTotal⟩ := (integerRadialWindow_eventually_symmetric ξ).exists
  rw [← hTotal]
  exact hasSum_sum_of_ne_finset_zero hOutside

/-- The infrared sum is the actual low pass at the terminal index, at every
nonzero frequency. Substituting the high index minus the gap gives its
manuscript low-frequency symbol. -/
theorem integerRadialWindow_lowPass_hasSum (j : ℤ) (ξ : E) (hξ : ξ ≠ 0) :
    HasSum (fun i : ℤ => if i ≤ j then integerRadialWindow i ξ else 0)
      (radialLowCutoff ((2 : ℝ)^j) ξ) := by
  obtain ⟨N, hLarge, hSmall⟩ := (eventually_radial_size ξ hξ).exists
  let length : ℕ := (j + (N : ℤ) + 1).toNat
  let I := Finset.Icc (j+1-(length : ℤ)) j
  let W := fun i : ℤ => if i ≤ j then integerRadialWindow i ξ else 0
  have hLow : j + 1 - (length : ℤ) ≤ -(N : ℤ) := by dsimp only [length]; omega
  have hOutside (i : ℤ) (hi : i ∉ I) : W i = 0 := by
    by_cases hTop : i ≤ j
    · simp only [W, if_pos hTop]
      by_contra hn
      have hmem := Finset.mem_Icc.mp (integerRadialWindow_nonzero_mem_symmetric ξ hLarge hSmall hn)
      exact hi (Finset.mem_Icc.mpr ⟨hLow.trans hmem.1, hTop⟩)
    · exact if_neg hTop
  have hSum : HasSum W (∑ i ∈ I, W i) := hasSum_sum_of_ne_finset_zero hOutside
  have hSame : (∑ i ∈ I, W i) = ∑ i ∈ I, integerRadialWindow i ξ :=
    Finset.sum_congr rfl (fun _ hi => if_pos (Finset.mem_Icc.mp hi).2)
  have hPow := zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
    (show j - (length : ℤ) + 1 ≤ -(N : ℤ) by omega)
  have hCut : 2 * (2 : ℝ)^(j - (length : ℤ)) ≤ ‖ξ‖ := by
    have hScaled : 2 * (2 : ℝ)^(j - (length : ℤ)) ≤ ((2 : ℝ)^N)⁻¹ := by
      simpa only [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one, zpow_neg,
        zpow_natCast, mul_comm] using hPow
    exact hScaled.trans hSmall
  rw [hSame, integerRadialWindow_block_sum, radialLowCutoff_eq_zero (by positivity) hCut,
    sub_zero] at hSum
  exact hSum

/-- The actual two-input partition is eventually exact at the same truncation
and vanishes whenever either input lies on its zero-frequency axis. -/
theorem integerRadialWindow_product_eventually_symmetric (p q : E) :
    ∀ᶠ N : ℕ in atTop,
      (∑ i ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ∑ j ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), integerRadialWindow i p * integerRadialWindow j q) =
        if p = 0 ∨ q = 0 then 0 else 1 := by
  classical
  filter_upwards [integerRadialWindow_eventually_symmetric p,
    integerRadialWindow_eventually_symmetric q] with N hp hq
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hp.2, hq.2]
  by_cases hp0 : p = 0 <;> by_cases hq0 : q = 0 <;> simp [hp0, hq0]

end Burnett.A05
