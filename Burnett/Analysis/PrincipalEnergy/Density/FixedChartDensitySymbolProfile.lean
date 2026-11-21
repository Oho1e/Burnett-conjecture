import Burnett.Analysis.PrincipalEnergy.Density.FixedChartDensitySandwich
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichMixed
import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichPureBase

set_option autoImplicit false
set_option maxHeartbeats 7800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ContDiff

private theorem norm_fderiv_smul_complex_le {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] [NormedSpace ℂ F] [IsScalarTower ℝ ℂ F]
    {u : Space → ℂ} {v : Space → F} {x : Space}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x) :
    ‖fderiv ℝ (fun y => u y • v y) x‖ ≤ ‖u x‖*‖fderiv ℝ v x‖ + ‖fderiv ℝ u x‖*‖v x‖ := by
  letI : NormedSpace ℂ (Space →L[ℝ] F) := ContinuousLinearMap.toNormedSpace
  have hR : ‖(fderiv ℝ u x).smulRight (v x)‖ ≤ ‖fderiv ℝ u x‖ * ‖v x‖ := by
    refine ((fderiv ℝ u x).smulRight (v x)).opNorm_le_bound (by positivity) fun y => ?_
    rw [ContinuousLinearMap.smulRight_apply, norm_smul]
    exact (mul_le_mul_of_nonneg_right ((fderiv ℝ u x).le_opNorm y) (norm_nonneg _)).trans_eq (by ring)
  change ‖fderiv ℝ (u • v) x‖ ≤ _
  rw [fderiv_smul hu hv]
  exact (norm_add_le _ _).trans (add_le_add (by rw [norm_smul]) hR)

private theorem firstBaseFrequencyOrderOne_mul_left {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) {v : Space → ℂ} (hv : ContDiff ℝ ∞ v)
    (S T : ℝ) (hS : 0 ≤ S) (hT : 0 ≤ T) (hV : ∀ x, ‖v x‖ ≤ S)
    (hD : ∀ x, ‖fderiv ℝ v x‖ ≤ T) :
    FirstBaseFrequencyOrderOne (fun x ξ => v x * a x ξ) := by
  have jet (n : ℕ) (x ξ : Space) :
      iteratedFDeriv ℝ n (fun ζ => v x * a x ζ) ξ = v x • iteratedFDeriv ℝ n (a x) ξ := by
    change iteratedFDeriv ℝ n (fun ζ => v x • a x ζ) ξ = _
    exact iteratedFDeriv_const_smul_apply' ((ha.frequency.smooth x).contDiffAt.of_le (by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)))
  refine ⟨⟨fun x => contDiff_const.mul (ha.frequency.smooth x), ?_⟩, ?_, ?_⟩
  · intro n
    obtain ⟨C, hC, bound⟩ := ha.frequency.order n
    refine ⟨S*C, mul_nonneg hS hC, fun x ξ => ?_⟩
    rw [jet, norm_smul, mul_assoc, mul_assoc]
    exact mul_le_mul (hV x) (bound x ξ) (by positivity) hS
  · intro n ξ
    simp_rw [jet]
    exact (hv.differentiable (by simp)).smul (ha.baseDiff n ξ)
  · intro n
    obtain ⟨C, hC, hFreq⟩ := ha.frequency.order n
    obtain ⟨D, hDN, hMixed⟩ := ha.order n
    refine ⟨S*D+T*C, by positivity, fun x ξ => ?_⟩
    simp_rw [jet]
    let W := (1 + ‖ξ‖)^n
    have hW : 0 ≤ W := by dsimp [W]; positivity
    have h0 := norm_fderiv_smul_complex_le ((hv.differentiable (by simp)) x) (ha.baseDiff n ξ x)
    change ‖fderiv ℝ (fun y => v y • iteratedFDeriv ℝ n (a y) ξ) x‖ * W ≤ (S*D+T*C)*(1+‖ξ‖)
    calc
      _ ≤ (‖v x‖*‖fderiv ℝ (fun y => iteratedFDeriv ℝ n (a y) ξ) x‖ +
          ‖fderiv ℝ v x‖*‖iteratedFDeriv ℝ n (a x) ξ‖)*W := mul_le_mul_of_nonneg_right h0 hW
      _ = ‖v x‖*(‖fderiv ℝ (fun y => iteratedFDeriv ℝ n (a y) ξ) x‖*W) +
          ‖fderiv ℝ v x‖*(‖iteratedFDeriv ℝ n (a x) ξ‖*W) := by ring
      _ ≤ S*(D*(1+‖ξ‖))+T*(C*(1+‖ξ‖)) :=
        add_le_add (mul_le_mul (hV x) (hMixed x ξ) (by positivity) hS)
          (mul_le_mul (hD x) (hFreq x ξ) (by positivity) hT)
      _ = _ := by ring

private theorem compactBaseOrderOne_mul_left {a : Space → Space → ℂ}
    (ha : CompactBaseOrderOne a) {v : Space → ℂ} (hv : ContDiff ℝ ∞ v)
    (hV : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x, ‖iteratedFDeriv ℝ n v x‖ ≤ C) :
    CompactBaseOrderOne (fun x ξ => v x * a x ξ) := by
  obtain ⟨K, hK, support⟩ := ha.support
  refine ⟨⟨K, hK, fun ξ => (closure_mono (fun x hx => ?_)).trans (support ξ)⟩,
    fun ξ => hv.mul (ha.smooth ξ), ?_⟩
  · change v x * a x ξ ≠ 0 at hx
    exact fun h => hx (mul_eq_zero_of_right _ h)
  · choose U hU hUbound using hV
    choose C hC hCbound using ha.order
    intro n
    let M := ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*U j*C (n-j)
    refine ⟨M, Finset.sum_nonneg (fun j _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hU j)) (hC (n-j))), fun x ξ => ?_⟩
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*‖iteratedFDeriv ℝ j v x‖*
          ‖iteratedFDeriv ℝ (n-j) (fun y => a y ξ) x‖ :=
        norm_iteratedFDeriv_mul_le hv (ha.smooth ξ) x (by exact_mod_cast le_top)
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ)*U j*(C (n-j)*(1+‖ξ‖)) := by
        exact Finset.sum_le_sum fun j _ => mul_le_mul
          (mul_le_mul_of_nonneg_left (hUbound j x) (Nat.cast_nonneg _)) (hCbound (n-j) x ξ)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hU j))
      _ = _ := by
        dsimp only [M]
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro j _
        ring

/-- The same density-conjugate symbol has the exact compact-base seminorms
used by the actual Lebesgue Calderón estimate on the fixed chart. -/
theorem fixedChartDensityConjugateSymbol_compactProfile {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hs : ContDiff ℝ ∞ (uncurry a))
    (hb : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (q : Space → ℝ) (hq : ContDiff ℝ ∞ q)
    (hV : ∀ n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ x,
      ‖iteratedFDeriv ℝ n (fun y => (q y : ℂ)^2) x‖ ≤ C)
    (χ : SchwartzMap Space ℂ) (hχ : HasCompactSupport (χ : Space → ℂ)) :
    FirstBaseFrequencyOrderOne (fixedChartDensityConjugateSymbol a q χ) ∧
    CompactBaseOrderOne (fixedChartDensityConjugateSymbol a q χ) ∧
    Continuous (uncurry (fixedChartDensityConjugateSymbol a q χ)) := by
  have hv : ContDiff ℝ ∞ (fun x => (q x : ℂ)^2) := (Complex.ofRealCLM.contDiff.comp hq).pow 2
  obtain ⟨S, hS, val⟩ := hV 0
  obtain ⟨T, hT, der⟩ := hV 1
  have hVal (x : Space) : ‖(q x : ℂ)^2‖ ≤ S := by
    simpa only [norm_iteratedFDeriv_zero] using val x
  have hDer (x : Space) : ‖fderiv ℝ (fun y => (q y : ℂ)^2) x‖ ≤ T := by
    calc
      _ = ‖iteratedFDeriv ℝ 0 (fderiv ℝ (fun y => (q y : ℂ)^2)) x‖ := norm_iteratedFDeriv_zero.symm
      _ = ‖iteratedFDeriv ℝ 1 (fun y => (q y : ℂ)^2) x‖ := norm_iteratedFDeriv_fderiv
      _ ≤ T := der x
  exact ⟨firstBaseFrequencyOrderOne_mul_left (cutoffSandwichSymbol_firstBaseFrequencyOrderOne ha hs χ)
      hv S T hS hT hVal hDer,
    compactBaseOrderOne_mul_left (cutoffSandwichSymbol_compactBaseOrderOne hs hb χ hχ) hv hV,
    (hv.continuous.comp continuous_fst).mul (cutoffSandwichSymbol_jointContinuous hs hb χ)⟩

end Burnett.Analysis.CarlesonEmbedding
