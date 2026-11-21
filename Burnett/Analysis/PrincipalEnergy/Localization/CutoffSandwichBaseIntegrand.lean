import Burnett.Analysis.PrincipalEnergy.Localization.FourierPhaseJets
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ContDiff FourierTransform

/-- The actual integrand of the sandwich symbol, with the base variable last. -/
def sandwichBaseIntegrand (a : Space → Space → ℂ) (χ : SchwartzMap Space ℂ) (ξ η x : Space) : ℂ :=
  𝓕 (χ : Space → ℂ) η •
    ((χ x * (Real.fourierChar (inner ℝ η x) : ℂ)) * a x (ξ + η))

theorem cutoffSandwichSymbol_eq_baseIntegral (a : Space → Space → ℂ) (χ : SchwartzMap Space ℂ)
    (x ξ : Space) : cutoffSandwichSymbol a χ x ξ = ∫ η, sandwichBaseIntegrand a χ ξ η x := by
  rw [cutoffSandwichSymbol, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with η
  simp only [sandwichBaseIntegrand, Circle.smul_def, smul_eq_mul]
  ring

private theorem norm_iteratedFDeriv_mul_of_uniform {u v : Space → ℂ} (hu : ContDiff ℝ ∞ u)
    (hv : ContDiff ℝ ∞ v) (x : Space) (n : ℕ) {S T : ℝ} (hS : 0 ≤ S)
    (hU : ∀ j ≤ n, ‖iteratedFDeriv ℝ j u x‖ ≤ S)
    (hV : ∀ j ≤ n, ‖iteratedFDeriv ℝ j v x‖ ≤ T) :
    ‖iteratedFDeriv ℝ n (fun y => u y * v y) x‖ ≤ (2 : ℝ)^n * S * T := by
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * ‖iteratedFDeriv ℝ j u x‖ *
        ‖iteratedFDeriv ℝ (n - j) v x‖ :=
      norm_iteratedFDeriv_mul_le hu hv x (by exact_mod_cast le_top)
    _ ≤ ∑ j ∈ Finset.range (n + 1), (n.choose j : ℝ) * S * T := by
      refine Finset.sum_le_sum fun j hj => ?_
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left (hU j (Nat.le_of_lt_succ (Finset.mem_range.mp hj))) (Nat.cast_nonneg _))
        (hV (n - j) (Nat.sub_le _ _)) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) hS)
    _ = _ := by
      simp only [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow, Nat.cast_ofNat]

/-- Every pure base derivative of the actual sandwich integrand has a
uniform order-one majorant, with one polynomial Fourier moment of the cutoff. -/
theorem exists_sandwichBaseIntegrand_derivative_bound {a : Space → Space → ℂ}
    (hSmooth : ContDiff ℝ ∞ (uncurry a))
    (hPure : ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ M * (1 + ‖ξ‖))
    (χ : SchwartzMap Space ℂ) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ η,
      ‖iteratedFDeriv ℝ n (sandwichBaseIntegrand a χ ξ η) x‖ ≤
        C * (1 + ‖ξ‖) * ((1 + ‖η‖)^(n + 1) * ‖𝓕 (χ : Space → ℂ) η‖) := by
  choose M hM hBound using hPure
  let S := ∑ j ∈ Finset.range (n + 1), SchwartzMap.seminorm ℝ 0 j χ
  let T := ∑ j ∈ Finset.range (n + 1), M j
  have hS : 0 ≤ S := Finset.sum_nonneg fun j _ =>
    (norm_nonneg _).trans (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ j (0 : Space))
  have hT : 0 ≤ T := Finset.sum_nonneg fun j _ => hM j
  have hSem (j : ℕ) (hj : j ≤ n) (x : Space) : ‖iteratedFDeriv ℝ j (χ : Space → ℂ) x‖ ≤ S :=
    (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ j x).trans
      (Finset.single_le_sum (fun k _ => (norm_nonneg _).trans
        (SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ k (0 : Space)))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  have hM_le (j : ℕ) (hj : j ≤ n) : M j ≤ T :=
    Finset.single_le_sum (fun k _ => hM k) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  let H : ℝ := 1 + 2 * Real.pi
  have hH : 0 ≤ H := by dsimp only [H]; positivity
  let C := (2 : ℝ)^n * ((2 : ℝ)^n * S * H^n) * T
  refine ⟨C, by dsimp only [C]; positivity, fun x ξ η => ?_⟩
  let Φ (y : Space) := (Real.fourierChar (inner ℝ η y) : ℂ)
  let q (y : Space) := χ y * Φ y
  let b (y : Space) := a y (ξ + η)
  let W := H * (1 + ‖η‖)
  let F := 𝓕 (χ : Space → ℂ) η
  have hW : 1 ≤ W := by
    dsimp only [W, H]
    nlinarith only [Real.pi_pos, norm_nonneg η, mul_nonneg Real.pi_pos.le (norm_nonneg η)]
  have hΦ : ContDiff ℝ ∞ Φ := (fourier_phase_contDiff_and_derivative_bound η).1
  have hb : ContDiff ℝ ∞ b := hSmooth.comp
    ((contDiff_id : ContDiff ℝ ∞ (id : Space → Space)).prodMk contDiff_const)
  have hΦBound (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j Φ x‖ ≤ W^n := by
    have hPhase : (2 * Real.pi) * ‖η‖ ≤ W := by dsimp only [W, H]; nlinarith [Real.pi_pos, norm_nonneg η]
    exact ((fourier_phase_contDiff_and_derivative_bound η).2 j x).trans
      ((pow_le_pow_left₀ (by positivity) hPhase j).trans (pow_le_pow_right₀ hW hj))
  have hqBound (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j q x‖ ≤ (2 : ℝ)^n * S * W^n := by
    have h := norm_iteratedFDeriv_mul_of_uniform (χ.smooth ⊤) hΦ x j hS
      (fun k hk => hSem k (hk.trans hj) x) (fun k hk => hΦBound k (hk.trans hj))
    exact h.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hj) hS) (by positivity))
  have hbBound (j : ℕ) (hj : j ≤ n) : ‖iteratedFDeriv ℝ j b x‖ ≤ T * (1 + ‖ξ + η‖) :=
    (hBound j x (ξ + η)).trans (mul_le_mul_of_nonneg_right (hM_le j hj) (by positivity))
  have hs : ContDiffAt ℝ n (fun y => q y * b y) x :=
    (((χ.smooth ⊤).mul hΦ).mul hb).contDiffAt.of_le (by exact_mod_cast le_top)
  change ‖iteratedFDeriv ℝ n (fun y => F • (q y * b y)) x‖ ≤ _
  rw [iteratedFDeriv_const_smul_apply' hs, norm_smul]
  have hqsc : 0 ≤ (2 : ℝ)^n * S * W^n := by positivity
  have hOrder := norm_iteratedFDeriv_mul_of_uniform ((χ.smooth ⊤).mul hΦ) hb x n hqsc hqBound hbBound
  have hWeight : 1 + ‖ξ + η‖ ≤ (1 + ‖ξ‖) * (1 + ‖η‖) := by
    nlinarith only [norm_add_le ξ η, mul_nonneg (norm_nonneg ξ) (norm_nonneg η)]
  calc
    _ ≤ ‖F‖ * ((2 : ℝ)^n * ((2 : ℝ)^n * S * W^n) * (T * (1 + ‖ξ + η‖))) :=
      mul_le_mul_of_nonneg_left hOrder (norm_nonneg _)
    _ ≤ ‖F‖ * ((2 : ℝ)^n * ((2 : ℝ)^n * S * W^n) * (T * ((1 + ‖ξ‖) * (1 + ‖η‖)))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWeight hT) (by positivity)) (norm_nonneg _)
    _ = _ := by dsimp only [C, W, F]; rw [mul_pow, pow_succ]; ring

end Burnett.Analysis.CarlesonEmbedding
