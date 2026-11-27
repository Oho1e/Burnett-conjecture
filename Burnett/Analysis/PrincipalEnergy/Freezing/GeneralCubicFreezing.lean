import Burnett.Analysis.PrincipalEnergy.Freezing.GeneralPrincipalFreezing
import Burnett.Analysis.PrincipalEnergy.Freezing.GeneralLowerCubicAction
import Burnett.Analysis.PrincipalEnergy.Freezing.GeneralFreezingTestL3

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 5000

noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open scoped ContDiff ENNReal

def euclideanFieldValueL3 {J : Type} [Fintype J] (z : J → SchwartzMap E ℂ) : ℝ :=
  (eLpNorm (fieldValueArray z) (ENNReal.ofReal 3) volume).toReal

/-- The three polarized placements of the real principal and lower
cubic polynomial with the standard symmetric action normalization. -/
def realCompleteCubicTest {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (z w : J → SchwartzMap E ℂ) : ℝ :=
  (realPrincipalVariation C z (fun i => w i) + realLowerCubicVariation C₀ C₁ z w) / 3

/-- The center action retains only the principal coefficients evaluated at
the center and uses the same symmetric action normalization. -/
def realFrozenCubicTest {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ) (c : E) (z w : J → SchwartzMap E ℂ) : ℝ :=
  realPrincipalVariation (fun a d i j k _ => C a d i j k c) z (fun i => w i) / 3

private theorem norm_div_three_le (x : ℝ) : ‖x / 3‖ₑ ≤ ‖x‖ₑ := by
  rw [← ofReal_norm, ← ofReal_norm, norm_div, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  exact ENNReal.ofReal_le_ofReal (div_le_self (norm_nonneg _) (by norm_num))

/-- Use the principal comparison and a first-order value bound for the actual complete action. -/
theorem exists_general_complete_cubic_freezing_bound_of_scalar_bounds {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (R : ℝ) (hR : 0 < R)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ) (B₀ : E → SchwartzMap E ℂ → SchwartzMap E ℂ)
    (principal : ∃ A : ℝ≥0∞, A < ⊤ ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∃ D : ℝ≥0∞, D < ⊤ ∧
      ∀ (c : E) (z : RealEnergyField J), tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        let X := euclideanFieldGradientNorm z.val
        let Y := eLpNorm (fieldValueArray z.val) (ENNReal.ofReal 3) volume
        let w (i : J) (x : E) := (-Complex.I) * B (z.val i) x
        let w₀ (i : J) (x : E) := (-Complex.I) * B₀ c (z.val i) x
        ‖realPrincipalVariation C z.val w - realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val w₀‖ₑ ≤
          A * ENNReal.ofReal ℓ * X ^ 3 + D * Y * X ^ 2)
    (value : ∃ K : ℝ≥0∞, K < ⊤ ∧ ∀ u : SchwartzMap E ℂ,
      eLpNorm (B u : E → ℂ) (ENNReal.ofReal 3) volume ≤
        K * (energyGradientNorm u + eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume)) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (c : E) (z : RealEnergyField J), tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        let w (i : J) := (-Complex.I) • B (z.val i)
        let w₀ (i : J) := (-Complex.I) • B₀ c (z.val i)
        |realCompleteCubicTest C C₀ C₁ z.val w - realFrozenCubicTest C c z.val w₀| ≤
          A * ℓ * euclideanFieldGradientL3 z.val ^ 3 +
          D * euclideanFieldValueL3 z.val * euclideanFieldGradientL3 z.val ^ 2 := by
  obtain ⟨A,hA,principal⟩ := principal
  obtain ⟨K,hK,valueBound⟩ := value
  obtain ⟨D, hD, lower⟩ := exists_general_lower_cubic_variation_bound C₀ C₁
  let P := ENNReal.ofReal (3 * R)
  let K₀ := D * (P + 1) * (K * (4 + P))
  have hP : P < ⊤ := ENNReal.ofReal_lt_top
  have hK₀ : K₀ < ⊤ := ENNReal.mul_lt_top
    (ENNReal.mul_lt_top hD (ENNReal.add_lt_top.mpr ⟨hP,by norm_num⟩))
    (ENNReal.mul_lt_top hK (ENNReal.add_lt_top.mpr ⟨by norm_num,hP⟩))
  refine ⟨A.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro ℓ hℓ hℓ₁
  obtain ⟨E₀, hE₀, patch⟩ := principal ℓ hℓ hℓ₁
  have hSum : E₀ + K₀ < ⊤ := ENNReal.add_lt_top.mpr ⟨hE₀,hK₀⟩
  refine ⟨(E₀ + K₀).toReal, ENNReal.toReal_nonneg, ?_⟩
  intro c z hz w w₀
  let p := ENNReal.ofReal 3
  let X := euclideanFieldGradientNorm z.val
  let Y := eLpNorm (fieldValueArray z.val) p volume
  have hX : X < ⊤ := euclideanFieldGradientNorm_lt_top z.val
  have Poincare : Y ≤ P * X := by
    refine (euclidean_field_local_poincare_eLpNorm z.val c (R * ℓ) (mul_pos hR hℓ) hz).trans ?_
    exact mul_le_mul_right' (ENNReal.ofReal_le_ofReal (by nlinarith)) X
  have hY : Y < ⊤ := lt_of_le_of_lt Poincare (ENNReal.mul_lt_top hP hX)
  obtain ⟨hZ, hDZ, hGradZ⟩ := separated_field_component_L3_bounds z.val
  let Z := K * (4 + P) * X
  have hW (i : J) : eLpNorm (w i : E → ℂ) p volume ≤ Z := by
    have hI : ‖(-Complex.I : ℂ)‖ₑ = 1 := by rw [← ofReal_norm, norm_neg, Complex.norm_I, ENNReal.ofReal_one]
    change eLpNorm ((-Complex.I) • (B (z.val i) : E → ℂ)) p volume ≤ Z
    rw [eLpNorm_const_smul, hI, one_mul]
    refine (valueBound (z.val i)).trans ?_
    have gradient : energyGradientNorm (z.val i) ≤ 4 * X := by simpa [Index, X] using hGradZ i
    refine (mul_le_mul_left' (add_le_add gradient ((hZ i).trans Poincare)) K).trans_eq ?_
    dsimp only [Z]
    ring
  have lowerBound : ‖realLowerCubicVariation C₀ C₁ z.val w‖ₑ ≤ K₀ * Y * X ^ 2 := by
    refine (lower z.val w X Y Z hZ (fun a i => hDZ (a,i)) hW).trans ?_
    have squared : Y ^ 2 ≤ (P * X) * Y := by rw [sq]; exact mul_le_mul_right' Poincare _
    have hFactor : Y ^ 2 + Y * X ≤ (P + 1) * Y * X :=
      (add_le_add squared le_rfl).trans_eq (by ring)
    exact (mul_le_mul_right' (mul_le_mul_left' hFactor D) Z).trans_eq (by dsimp only [K₀, Z]; ring)
  have principalBound : ‖realPrincipalVariation C z.val (fun i => w i) -
      realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val (fun i => w₀ i)‖ₑ ≤
      A * ENNReal.ofReal ℓ * X ^ 3 + E₀ * Y * X ^ 2 := by
    simpa only [w, w₀, SchwartzMap.smul_apply, smul_eq_mul] using patch c z hz
  let U := realPrincipalVariation C z.val (fun i => w i)
  let V := realPrincipalVariation (fun a d i j k _ => C a d i j k c) z.val (fun i => w₀ i)
  let W := realLowerCubicVariation C₀ C₁ z.val w
  let E := realCompleteCubicTest C C₀ C₁ z.val w - realFrozenCubicTest C c z.val w₀
  have same : E = ((U - V) + W) / 3 := by
    change (U + W) / 3 - V / 3 = _
    ring
  have estimate : ‖E‖ₑ ≤ A * ENNReal.ofReal ℓ * X ^ 3 + (E₀ + K₀) * Y * X ^ 2 := by
    rw [same]
    exact (((norm_div_three_le _).trans (enorm_add_le _ _)).trans
      (add_le_add principalBound lowerBound)).trans_eq (by ring)
  have finite₁ : A * ENNReal.ofReal ℓ * X ^ 3 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hA ENNReal.ofReal_lt_top) (ENNReal.pow_lt_top hX)
  have finite₂ : (E₀ + K₀) * Y * X ^ 2 < ⊤ :=
    ENNReal.mul_lt_top (ENNReal.mul_lt_top hSum hY) (ENNReal.pow_lt_top hX)
  have realBound := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨finite₁,finite₂⟩).ne estimate
  rw [← ofReal_norm, ENNReal.toReal_ofReal (norm_nonneg _), Real.norm_eq_abs,
    ENNReal.toReal_add finite₁.ne finite₂.ne] at realBound
  simpa only [E, X, Y, p, euclideanFieldValueL3, euclideanFieldGradientL3, ENNReal.toReal_mul,
    ENNReal.toReal_pow, ENNReal.toReal_ofReal hℓ.le] using realBound

/-- General finite-field quantitative freezing for the actual complete
cubic action in a compact coordinate Weyl representation. All lower
monomials of total field derivative count zero or one are included. -/
theorem exists_general_complete_cubic_freezing_bound {J : Type} [Fintype J]
    (C : Index → Index → J → J → J → E → ℝ)
    (hSmooth : ∀ a d i j k, ContDiff ℝ ∞ (C a d i j k))
    (hCompact : ∀ a d i j k, HasCompactSupport (C a d i j k))
    (hSymm : ∀ a d i j k, C a d i j k = C d a i k j)
    (C₀ : J × J × J → SchwartzMap E ℂ) (C₁ : Index × J × J × J → SchwartzMap E ℂ)
    (R L M : ℝ) (hR : 0 < R) (hL : 0 ≤ L)
    (hGrad : ∀ a d i j k x, ‖fderiv ℝ (C a d i j k) x‖ ≤ L)
    (hValue : ∀ a d i j k x, ‖C a d i j k x‖ ≤ M)
    (test : CompactScalarWeylTest)
    (B : SchwartzMap E ℂ → SchwartzMap E ℂ) (B₀ : E → SchwartzMap E ℂ → SchwartzMap E ℂ)
    (hB : ∀ u, (B u : E → ℂ) = test.action u)
    (hB₀ : ∀ c u, (B₀ c u : E → ℂ) = test.frozenAction c u) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ℓ : ℝ, 0 < ℓ → ℓ ≤ 1 → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (c : E) (z : RealEnergyField J), tsupport (fieldValueArray z.val) ⊆ ball c (R * ℓ) →
        let w (i : J) := (-Complex.I) • B (z.val i)
        let w₀ (i : J) := (-Complex.I) • B₀ c (z.val i)
        |realCompleteCubicTest C C₀ C₁ z.val w - realFrozenCubicTest C c z.val w₀| ≤
          A * ℓ * euclideanFieldGradientL3 z.val ^ 3 +
          D * euclideanFieldValueL3 z.val * euclideanFieldGradientL3 z.val ^ 2 := by
  exact exists_general_complete_cubic_freezing_bound_of_scalar_bounds C C₀ C₁ R hR B B₀
    (exists_general_principal_freezing_bound C hSmooth hCompact hSymm R L M hR hL hGrad hValue test B B₀ hB hB₀)
    (test.exists_action_value_L3_bound B hB)

end Burnett.A03
