import Burnett.Analysis.CubicEnergy.HighSlotCommutator.LowCartesianSymbol

set_option autoImplicit false
set_option maxHeartbeats 4600000

noncomputable section

open Set Metric Filter
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Topology

namespace Burnett.A06

private def orderOneWeight (x : Joint) : ℝ := 1 + ‖x.1‖ + ‖x.2‖

/-- The high-frequency contribution reduces to one normalized low-ratio
window. A second finite window accounts for the fixed high infrared cutoff. -/
theorem regularizedLowCartesianSymbol_seminorm_of_windows
    (n : ℕ) (η χ : ℝ → ℝ) (c : Joint → ℂ) {ρ R Cunit Cfinite : ℝ}
    (hρ : 0 ≤ ρ) (hR : 1 ≤ R) (hηone : ∀ s ≥ R, η s = 1)
    (hχ : ContDiff ℝ n χ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ n c V) (hu : 0 ≤ Cunit) (hf : 0 ≤ Cfinite)
    (unitBound : ∀ x ∈ closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n (lowCartesianSymbol χ c) x‖ ≤ Cunit)
    (finiteBound : ∀ x ∈ closedBall (0 : E) (ρ*R) ×ˢ closedBall (0 : E) R,
      ‖iteratedFDeriv ℝ n (regularizedLowCartesianSymbol η χ c) x‖ ≤ Cfinite)
    (x : Joint) :
    ‖iteratedFDeriv ℝ n (regularizedLowCartesianSymbol η χ c) x‖ *
      (1 + ‖x.1‖ + ‖x.2‖)^n ≤
      max (Cunit * (2+ρ)^n) (Cfinite * (1+(ρ+1)*R)^n) * (1 + ‖x.1‖ + ‖x.2‖) := by
  let a := ‖x.2‖
  let W := orderOneWeight x
  let K := max (Cunit * (2+ρ)^n) (Cfinite * (1+(ρ+1)*R)^n)
  have hW : 1 ≤ W := by
    dsimp [W, orderOneWeight]
    linarith only [norm_nonneg x.1, norm_nonneg x.2]
  have hpW : 0 ≤ W := zero_le_one.trans hW
  have hK : 0 ≤ K :=
    (mul_nonneg hu (pow_nonneg (by positivity) n)).trans (le_max_left _ _)
  change ‖iteratedFDeriv ℝ n (regularizedLowCartesianSymbol η χ c) x‖ * W^n ≤ K*W
  by_cases hcone : ‖x.1‖ ≤ ρ*a
  · by_cases hhigh : R < a
    · have ha : 0 < a := zero_lt_one.trans (hR.trans_lt hhigh)
      have hneq : x.2 ≠ 0 := norm_pos_iff.mp ha
      let u := normalizedHighPair x
      have hu1 : ‖u.2‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hneq
      have hu0 : u.2 ≠ 0 := norm_ne_zero_iff.mp (hu1.trans_ne one_ne_zero)
      have hu2 : ‖u.1‖ ≤ ρ := by
        change ‖a⁻¹ • x.1‖ ≤ ρ
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr ha.le), mul_comm, ← div_eq_mul_inv]
        exact (div_le_iff₀ ha).mpr hcone
      have hunit := unitBound u ⟨mem_closedBall_zero_iff.mpr hu2, mem_sphere_zero_iff_norm.mpr hu1⟩
      have hr : a • u = x := by
        change a • (a⁻¹ • x) = x
        rw [smul_smul, mul_inv_cancel₀ ha.ne', one_smul]
      have scale := lowCartesianSymbol_iteratedFDeriv_smul n χ c hρ hχ hcut hV hContains hc a ha u hu0
      have scaleNorm := congrArg norm scale
      rw [hr, norm_smul, norm_smul, Real.norm_of_nonneg (pow_nonneg ha.le _),
        Real.norm_of_nonneg ha.le] at scaleNorm
      have near : ∀ᶠ y : Joint in 𝓝 x, R < ‖y.2‖ :=
        (isOpen_lt continuous_const continuous_snd.norm).mem_nhds hhigh
      have agree : regularizedLowCartesianSymbol η χ c =ᶠ[𝓝 x] lowCartesianSymbol χ c := by
        filter_upwards [near] with y hy
        simp only [regularizedLowCartesianSymbol, hηone _ hy.le, one_smul]
      have same := (agree.iteratedFDeriv ℝ n).eq_of_nhds
      have hWa : W ≤ (2+ρ)*a := by
        have a1 : 1 ≤ a := hR.trans hhigh.le
        dsimp [W, orderOneWeight]
        change 1 + ‖x.1‖ + a ≤ _
        linarith only [hcone,a1]
      have haW : a ≤ W := by
        dsimp [W, orderOneWeight, a]
        linarith only [norm_nonneg x.1]
      rw [same]
      calc
        _ ≤ ‖iteratedFDeriv ℝ n (lowCartesianSymbol χ c) x‖ * ((2+ρ)*a)^n :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hpW hWa _) (norm_nonneg _)
        _ = (2+ρ)^n * (a * ‖iteratedFDeriv ℝ n (lowCartesianSymbol χ c) u‖) := by
          rw [mul_pow]
          rw [show ‖iteratedFDeriv ℝ n (lowCartesianSymbol χ c) x‖ * ((2+ρ)^n * a^n) =
            (2+ρ)^n * (a^n * ‖iteratedFDeriv ℝ n (lowCartesianSymbol χ c) x‖) by ring]
          rw [scaleNorm]
        _ ≤ (Cunit * (2+ρ)^n) * a := by
          calc
            _ ≤ (2+ρ)^n * (a * Cunit) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hunit ha.le) (by positivity)
            _ = _ := by ring
        _ ≤ K*W :=
          mul_le_mul (le_max_left _ _) haW ha.le hK
    · have hbound : a ≤ R := le_of_not_gt hhigh
      have hxK : x ∈ closedBall (0 : E) (ρ*R) ×ˢ closedBall (0 : E) R :=
        ⟨mem_closedBall_zero_iff.mpr (hcone.trans (mul_le_mul_of_nonneg_left hbound hρ)),
          mem_closedBall_zero_iff.mpr hbound⟩
      have hW' : W ≤ 1+(ρ+1)*R := by
        have pBound := hcone.trans (mul_le_mul_of_nonneg_left hbound hρ)
        dsimp [W, orderOneWeight]
        change 1 + ‖x.1‖ + a ≤ _
        linarith only [pBound,hbound]
      calc
        _ ≤ Cfinite * (1+(ρ+1)*R)^n :=
          mul_le_mul (finiteBound x hxK) (pow_le_pow_left₀ hpW hW' _) (pow_nonneg hpW _) hf
        _ ≤ K := le_max_right _ _
        _ ≤ K*W := le_mul_of_one_le_right hK hW
  · have near : ∀ᶠ y : Joint in 𝓝 x, ρ * ‖y.2‖ < ‖y.1‖ :=
      (isOpen_lt (continuous_const.mul continuous_snd.norm) continuous_fst.norm).mem_nhds
        (lt_of_not_ge hcone)
    have vanish : regularizedLowCartesianSymbol η χ c =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [near] with y hy
      simp only [regularizedLowCartesianSymbol, lowCartesianSymbol_eq_zero_outside χ c hρ hcut hy.le,
        smul_zero]
    have zero := (vanish.iteratedFDeriv ℝ n).eq_of_nhds
    rw [zero, iteratedFDeriv_zero_fun, Pi.zero_apply, norm_zero, zero_mul]
    exact mul_nonneg hK hpW

/-- For each derivative order the fixed high infrared regularizer gives
the order-one Cartesian estimate throughout the two-frequency space. -/
theorem exists_regularizedLowCartesianSymbol_orderOne_bound
    (n : ℕ) (η χ : ℝ → ℝ) (c : Joint → ℂ) {r ρ R : ℝ}
    (hr : 0 < r) (hρ : 0 ≤ ρ) (hR : 1 ≤ R)
    (hη : ContDiff ℝ n η) (hηzero : ∀ s ≤ r, η s = 0) (hηone : ∀ s ≥ R, η s = 1)
    (hχ : ContDiff ℝ n χ) (hcut : ∀ s ≥ ρ^2, χ s = 0)
    {V : Set Joint} (hV : IsOpen V)
    (hContains : closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1 ⊆ V)
    (hc : ContDiffOn ℝ n c V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : Joint,
      ‖iteratedFDeriv ℝ n (regularizedLowCartesianSymbol η χ c) x‖ *
        (1 + ‖x.1‖ + ‖x.2‖)^n ≤ C * (1 + ‖x.1‖ + ‖x.2‖) := by
  let U : Set Joint := {x | x.2 ≠ 0}
  let K := closedBall (0 : E) ρ ×ˢ sphere (0 : E) 1
  let L := closedBall (0 : E) (ρ*R) ×ˢ closedBall (0 : E) R
  have hU : IsOpen U := isOpen_ne_fun continuous_snd continuous_const
  have hbare : ContDiffOn ℝ n (lowCartesianSymbol χ c) U := fun _ hx =>
    (lowCartesianSymbol_contDiffAt χ c hρ hχ hcut hV hContains hc hx).contDiffWithinAt
  have hregular := regularizedLowCartesianSymbol_contDiff η χ c hr hρ hη hηzero hχ hcut hV hContains hc
  have bCont : ContinuousOn (iteratedFDeriv ℝ n (lowCartesianSymbol χ c)) U :=
    (hbare.continuousOn_iteratedFDerivWithin le_rfl hU.uniqueDiffOn).congr
      (iteratedFDerivWithin_of_isOpen n hU).symm
  have sub : K ⊆ U := by
    intro x hx
    exact norm_ne_zero_iff.mp ((mem_sphere_zero_iff_norm.mp hx.2).trans_ne one_ne_zero)
  have compactK : IsCompact K := (isCompact_closedBall (0 : E) ρ).prod (isCompact_sphere (0 : E) 1)
  have compactL : IsCompact L := (isCompact_closedBall (0 : E) (ρ*R)).prod (isCompact_closedBall (0 : E) R)
  obtain ⟨A,hA⟩ := compactK.bddAbove_image (bCont.norm.mono sub)
  obtain ⟨B,hB⟩ := compactL.bddAbove_image
    (hregular.continuous_iteratedFDeriv le_rfl).norm.continuousOn
  have hA0 : 0 ≤ max A 0 := le_max_right _ _
  have hB0 : 0 ≤ max B 0 := le_max_right _ _
  have C0 : 0 ≤ max A 0 * (2+ρ)^n := by positivity
  refine ⟨max (max A 0 * (2+ρ)^n) (max B 0 * (1+(ρ+1)*R)^n),
    C0.trans (le_max_left _ _), ?_⟩
  exact regularizedLowCartesianSymbol_seminorm_of_windows n η χ c hρ hR hηone hχ hcut
    hV hContains hc hA0 hB0
    (fun x hx => (hA (mem_image_of_mem _ hx)).trans (le_max_left _ _))
    (fun x hx => (hB (mem_image_of_mem _ hx)).trans (le_max_left _ _))

end Burnett.A06
