import Burnett.Analysis.AllScaleTransfer.ActualComparableBoxPartition

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.A05

open Set
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open scoped ContDiff

/-- The endpoint symbol on the two signed normalized directions. -/
def radianEndpointAngular (M₀ : Joint → ℂ) (p q : E) : ℂ :=
  M₀ (‖p‖⁻¹ • p, ‖q‖⁻¹ • q)

private theorem unitDirection_pos_smul (x : E) {t : ℝ} (ht : 0 < t) :
    ‖t • x‖⁻¹ • (t • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_of_nonneg ht.le, smul_smul, mul_inv_rev, mul_assoc, inv_mul_cancel₀ ht.ne', mul_one]

def lowPassCorrectionDifference (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (j : ℤ) (p q : E) : ℝ :=
  χ₀ (‖A p‖ / ‖A q‖) - radialLowCutoff ((2 : ℝ)^j/(2 : ℝ)^C) p

/-- The genuine correction before the first input is decomposed radially. -/
def radianLowPassCorrectionBlock (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (M₀ : Joint → ℂ) (j : ℤ) (x : Joint) : ℂ :=
  radianEndpointAngular M₀ x.1 x.2 *
    ((integerRadialWindow j x.2 : ℂ) * (lowPassCorrectionDifference χ₀ A C j x.1 x.2 : ℂ))

/-- The actual normalized box profile of the signed offset k. -/
def normalizedLowPassCorrection (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (M₀ : Joint → ℂ) (k : ℤ) (z : BoxSpace) : ℂ :=
  let ζ := firstInput z
  let υ := secondInput z
  radianEndpointAngular M₀ ζ υ *
    ((χ₀ ((2 : ℝ)^k * (‖A ζ‖ / ‖A υ‖)) -
      radialBallBump ((2 : ℝ)^((C : ℤ)+k) • ζ) : ℝ) : ℂ)

theorem normalizedLowPassCorrection_at_dyadic_pair (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (M₀ : Joint → ℂ) (k j : ℤ) (ζ υ : E) :
    let p := (2 : ℝ)^(j+k) • ζ
    let q := (2 : ℝ)^j • υ
    normalizedLowPassCorrection χ₀ A C M₀ k (joinedInputs ζ υ) =
      radianEndpointAngular M₀ p q * (lowPassCorrectionDifference χ₀ A C j p q : ℂ) := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hj : 0 < (2 : ℝ)^j := by positivity
  have hjk : 0 < (2 : ℝ)^(j+k) := by positivity
  have ratio : ‖A ((2 : ℝ)^(j+k) • ζ)‖ / ‖A ((2 : ℝ)^j • υ)‖ =
      (2 : ℝ)^k * (‖A ζ‖ / ‖A υ‖) := by
    rw [map_smul, map_smul, norm_smul, norm_smul, Real.norm_of_nonneg hj.le,
      Real.norm_of_nonneg hjk.le, zpow_add₀ h2, mul_assoc, mul_div_mul_left _ _ hj.ne', mul_div_assoc]
  have radius : radialLowCutoff ((2 : ℝ)^j/(2 : ℝ)^C) ((2 : ℝ)^(j+k) • ζ) =
      radialBallBump ((2 : ℝ)^((C : ℤ)+k) • ζ) := by
    unfold radialLowCutoff
    rw [smul_smul]
    have hScale : ((2 : ℝ)^j/(2 : ℝ)^C)⁻¹ * (2 : ℝ)^(j+k) = (2 : ℝ)^((C : ℤ)+k) := by
      rw [inv_div, zpow_add₀ h2, ← mul_assoc, div_mul_cancel₀ _ hj.ne',
        zpow_add₀ h2, zpow_natCast]
    rw [hScale]
  simp only [normalizedLowPassCorrection, lowPassCorrectionDifference, radianEndpointAngular,
    firstInput_joined, secondInput_joined, unitDirection_pos_smul ζ hjk,
    unitDirection_pos_smul υ hj, ratio, radius]

/-- The paper's actual endpoint factor and cutoff correction at both original frequencies. -/
theorem normalizedLowPassCorrection_at_frequencies (χ₀ : ℝ → ℝ) (A : E ≃L[ℝ] E)
    (C : ℕ) (M₀ : Joint → ℂ) (k j : ℤ) (p q : E) :
    normalizedLowPassCorrection χ₀ A C M₀ k
      (joinedInputs ((2 : ℝ)^(-(j+k)) • p) ((2 : ℝ)^(-j) • q)) =
      radianEndpointAngular M₀ p q * (lowPassCorrectionDifference χ₀ A C j p q : ℂ) := by
  have cancel (l : ℤ) (x : E) : (2 : ℝ)^l • ((2 : ℝ)^(-l) • x) = x := by
    rw [smul_smul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero, one_smul]
  simpa only [cancel] using normalizedLowPassCorrection_at_dyadic_pair χ₀ A C M₀ k j
    ((2 : ℝ)^(-(j+k)) • p) ((2 : ℝ)^(-j) • q)

def correctionThirdLower (L U u : ℝ) : ℝ := min 1 ((1-u)*L/(2*U))
def correctionThirdUpper (L U u : ℝ) : ℝ := max 2 (2*(1+u*U/L))

private theorem correctionThirdLower_pos (L U u : ℝ) (hL : 0 < L) (hU : 0 < U) (hu : u < 1) :
    0 < correctionThirdLower L U u :=
  lt_min zero_lt_one (div_pos (mul_pos (sub_pos.mpr hu) hL) (mul_pos two_pos hU))

private theorem correctionThirdLower_le_upper (L U u : ℝ) :
    correctionThirdLower L U u ≤ correctionThirdUpper L U u :=
  (min_le_left _ _).trans ((show (1 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _))

def lowPassCorrectionThirdProfile (L U u : ℝ) (hL : 0 < L) (hU : 0 < U) (hu : u < 1) :
    SchwartzMap E ℂ :=
  comparableThirdSchwartzProfile (correctionThirdLower L U u) (correctionThirdUpper L U u)
    (correctionThirdLower_pos L U u hL hU hu) (correctionThirdLower_le_upper L U u)

/-- The fixed third annulus for nonzero low-pass correction blocks.
Its lower radius uses the physical small ratio and the global upper bound
for the same A, so no cone assumption on the third input is needed. -/
theorem lowPassCorrection_signedThird_mem_annulus (A : E ≃L[ℝ] E)
    {L U u r : ℝ} (hL : 0 < L) (hU : 0 < U) (hu : 0 ≤ u) (hu1 : u < 1) (hr : 0 < r)
    (hUpper : ∀ x : E, ‖A x‖ ≤ U*‖x‖)
    {p q : E} (hp : L*‖p‖ ≤ ‖A p‖) (hq : L*‖q‖ ≤ ‖A q‖)
    (hAnn : r/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*r)
    (hRatio : ‖A p‖ / ‖A q‖ < u) :
    ‖-(p+q)‖ ∈ Set.Icc (correctionThirdLower L U u*r) (correctionThirdUpper L U u*r) := by
  let w := -(p+q)
  have hpU : 0 < 1-u := sub_pos.mpr hu1
  have hAq : 0 < ‖A q‖ := (mul_pos hL (lt_of_lt_of_le (by positivity) hAnn.1)).trans_le hq
  have small : ‖A p‖ < u*‖A q‖ := (div_lt_iff₀ hAq).mp hRatio
  have hTriangle : ‖A q‖ ≤ ‖A w‖ + ‖A p‖ := by
    have h := norm_sub_le (A (p+q)) (A p)
    rw [map_add, add_sub_cancel_left] at h
    simpa only [w, map_neg, norm_neg, map_add] using h
  have phyLower : (1-u)*‖A q‖ ≤ ‖A w‖ := by linarith only [hTriangle, small]
  have lower : ((1-u)*L/(2*U))*r ≤ ‖w‖ := by
    apply (mul_le_mul_iff_right₀ hU).mp
    calc
      _ = (1-u)*(L*(r/2)) := by field_simp [hU.ne']
      _ ≤ (1-u)*‖A q‖ := mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hAnn.1 hL.le).trans hq) hpU.le
      _ ≤ ‖A w‖ := phyLower
      _ ≤ _ := hUpper w
  have plen : ‖p‖ ≤ (u*U/L)*‖q‖ := by
    apply (mul_le_mul_iff_right₀ hL).mp
    calc
      L*‖p‖ ≤ ‖A p‖ := hp
      _ ≤ u*‖A q‖ := small.le
      _ ≤ u*(U*‖q‖) := mul_le_mul_of_nonneg_left (hUpper q) hu
      _ = L*((u*U/L)*‖q‖) := by field_simp [hL.ne']
  have upper : ‖w‖ ≤ 2*(1+u*U/L)*r := calc
    _ ≤ ‖p‖+‖q‖ := by simpa only [w, norm_neg] using norm_add_le p q
    _ ≤ (u*U/L)*‖q‖+‖q‖ := add_le_add_right plen _
    _ = (1+u*U/L)*‖q‖ := by ring
    _ ≤ (1+u*U/L)*(2*r) := mul_le_mul_of_nonneg_left hAnn.2 (by positivity)
    _ = _ := by ring
  exact ⟨(mul_le_mul_of_nonneg_right (min_le_right _ _) hr.le).trans lower,
    upper.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hr.le)⟩

theorem lowPassCorrectionThirdProfile_at_dyadic (A : E ≃L[ℝ] E)
    {L U u : ℝ} (hL : 0 < L) (hU : 0 < U) (hu : 0 ≤ u) (hu1 : u < 1)
    (hUpper : ∀ x : E, ‖A x‖ ≤ U*‖x‖)
    {p q : E} (hp : L*‖p‖ ≤ ‖A p‖) (hq : L*‖q‖ ≤ ‖A q‖) (j : ℤ)
    (hAnn : (2 : ℝ)^j/2 ≤ ‖q‖ ∧ ‖q‖ ≤ 2*(2 : ℝ)^j)
    (hRatio : ‖A p‖ / ‖A q‖ < u) :
    lowPassCorrectionThirdProfile L U u hL hU hu1 ((2 : ℝ)^(-j) • (-(p+q))) = 1 := by
  have hr : 0 < (2 : ℝ)^j := by positivity
  have band := lowPassCorrection_signedThird_mem_annulus A hL hU hu hu1 hr hUpper hp hq hAnn hRatio
  unfold lowPassCorrectionThirdProfile
  rw [zpow_neg, comparableThirdSchwartzProfile_scaled,
    comparableThirdCutoff_eq_one (correctionThirdLower_pos L U u hL hU hu1)
      ((correctionThirdLower_pos L U u hL hU hu1).trans_le (correctionThirdLower_le_upper L U u))
      hr band, Complex.ofReal_one]

end Burnett.A05
