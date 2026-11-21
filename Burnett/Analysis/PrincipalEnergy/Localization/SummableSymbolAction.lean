import Burnett.Analysis.PrincipalEnergy.Localization.SummableSymbolBounds
import Burnett.Analysis.PrincipalEnergy.Localization.ActualPartitionPairs
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 5300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Filter Function MeasureTheory
open Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped FourierTransform ComplexConjugate

theorem integral_real_weighted_tsum {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖))
    (f : ℕ → α → ℂ) {D : α → ℝ} (hD : Integrable D μ)
    (hM : ∀ i, AEStronglyMeasurable (f i) μ) (h : ∀ i x, ‖f i x‖ ≤ D x) :
    (∫ x, ∑' i, u i • f i x ∂μ) = ∑' i, u i • (∫ x, f i x ∂μ) := by
  have hI (i : ℕ) : Integrable (f i) μ := hD.mono' (hM i) (.of_forall (h i))
  have hIu (i : ℕ) : Integrable (fun x => u i • f i x) μ := (hI i).smul (u i)
  have hS : Summable (fun i => ∫ x, ‖u i • f i x‖ ∂μ) := by
    refine .of_nonneg_of_le (fun i => integral_nonneg fun _ => norm_nonneg _) (fun i => ?_)
      (hu.mul_right (∫ x, D x ∂μ))
    rw [← integral_const_mul]
    exact integral_mono (hIu i).norm (hD.const_mul _)
      (fun x => by rw [norm_smul]; exact mul_le_mul_of_nonneg_left (h i x) (norm_nonneg _))
  rw [← integral_tsum_of_summable_integral_norm hIu hS]
  simp only [integral_smul]

private theorem firstOrderAction_integral_formula (a : Space → Space → ℂ)
    (f : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction a f x = ∫ ξ,
      Real.fourierChar (inner ℝ ξ x) • (a x ξ * (SchwartzMap.fourierTransformCLM ℂ f) ξ) := by
  rw [firstOrderAction, Real.fourierIntegralInv_eq]
  rfl

/-- A fixed Schwartz input has one pointwise bound for every symbol in the
family and every spatial point. -/
theorem uniformCompactSymbolFamily_action_bound {ι : Type*} {a : ι → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) (f : SchwartzMap Space ℂ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ i x, ‖firstOrderAction (a i) f x‖ ≤ M := by
  obtain ⟨A, hA, hOrder⟩ := ha.frequencyOrder 0
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let D (ξ : Space) := A * ((1 + ‖ξ‖) * ‖F ξ‖)
  have hD : Integrable D (volume : Measure Space) := by
    simpa only [D, pow_one] using (integrable_schwartz_weighted F 1).const_mul A
  refine ⟨∫ ξ, D ξ, integral_nonneg (fun ξ => by dsimp [D]; positivity), fun i x => ?_⟩
  rw [firstOrderAction_integral_formula]
  apply norm_integral_le_of_norm_le hD
  filter_upwards with ξ
  have hVal : ‖a i x ξ‖ ≤ A * (1 + ‖ξ‖) := by
    simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hOrder i x ξ
  change ‖Real.fourierChar (inner ℝ ξ x) • (a i x ξ * F ξ)‖ ≤ D ξ
  dsimp only [D]
  rw [Circle.norm_smul, norm_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hVal (norm_nonneg _)

theorem firstOrderAction_continuous_for_family {ι : Type*} {a : ι → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) (i : ι) (f : SchwartzMap Space ℂ) :
    Continuous (firstOrderAction (a i) f) := by
  have ha₀ : FrequencyOrderOne (a i) := by
    refine ⟨ha.smoothFrequency i, fun n => ?_⟩
    obtain ⟨C, hC, hb⟩ := ha.frequencyOrder n
    exact ⟨C, hC, hb i⟩
  exact (firstOrderAction_continuous_and_bounded ha₀ (ha.jointlyContinuous i) f).1

theorem mul_real_weighted_tsum (p : ℂ) (u : ℕ → ℝ) (f : ℕ → ℂ) :
    p * (∑' i, u i • f i) = ∑' i, u i • (p * f i) := by
  simp only [Algebra.smul_def]
  rw [← tsum_mul_left]
  exact tsum_congr fun i => by ring

theorem real_weighted_tsum_mul (p : ℂ) (u : ℕ → ℝ) (f : ℕ → ℂ) :
    (∑' i, u i • f i) * p = ∑' i, u i • (f i * p) := by
  simp only [Algebra.smul_def]
  rw [← tsum_mul_right]
  exact tsum_congr fun i => by ring

/-- Quantization commutes with real absolutely summable superposition
on the uniform compact symbol family. -/
theorem firstOrderAction_summableSymbolSum {a : ℕ → Space → Space → ℂ} (ha : UniformCompactSymbolFamily a)
    {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖)) (f : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction (summableSymbolSum a u) f x = ∑' i, u i • firstOrderAction (a i) f x := by
  obtain ⟨A, _, hOrder⟩ := ha.frequencyOrder 0
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let P (i : ℕ) (ξ : Space) := Real.fourierChar (inner ℝ ξ x) • (a i x ξ * F ξ)
  let D (ξ : Space) := A * ((1 + ‖ξ‖) * ‖F ξ‖)
  have hD : Integrable D (volume : Measure Space) := by
    simpa only [D, pow_one] using (integrable_schwartz_weighted F 1).const_mul A
  have hM (i : ℕ) : AEStronglyMeasurable (P i) (volume : Measure Space) :=
    ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      ((ha.smoothFrequency i x).continuous.mul F.continuous)).aestronglyMeasurable
  have hBound (i : ℕ) (ξ : Space) : ‖P i ξ‖ ≤ D ξ := by
    have hVal : ‖a i x ξ‖ ≤ A * (1 + ‖ξ‖) := by
      simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hOrder i x ξ
    simp only [P, D, Circle.norm_smul, norm_mul, ← mul_assoc A]
    exact mul_le_mul_of_nonneg_right hVal (norm_nonneg _)
  rw [firstOrderAction_integral_formula]
  calc
    _ = ∫ ξ, ∑' i, u i • P i ξ := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [P, F, summableSymbolSum, Circle.smul_def, smul_eq_mul, real_weighted_tsum_mul,
        mul_real_weighted_tsum]
    _ = ∑' i, u i • (∫ ξ, P i ξ) := integral_real_weighted_tsum hu P hD hM hBound
    _ = _ := tsum_congr fun i => congrArg (fun z : ℂ => u i • z)
      (firstOrderAction_integral_formula (a i) f x).symm

/-- Testing commutes with real absolutely summable superposition on the
same actual Fourier action. -/
theorem integral_pair_firstOrderAction_summableSymbolSum {a : ℕ → Space → Space → ℂ}
    (ha : UniformCompactSymbolFamily a) {u : ℕ → ℝ} (hu : Summable (fun i => ‖u i‖))
    (f g : SchwartzMap Space ℂ) :
    (∫ x, conj (g x) * firstOrderAction (summableSymbolSum a u) f x) =
      ∑' i, u i • (∫ x, conj (g x) * firstOrderAction (a i) f x) := by
  obtain ⟨M, hM, hb⟩ := uniformCompactSymbolFamily_action_bound ha f
  have hD : Integrable (fun x => M * ‖g x‖) := g.integrable.norm.const_mul M
  simp_rw [firstOrderAction_summableSymbolSum ha hu, mul_real_weighted_tsum]
  refine integral_real_weighted_tsum hu (fun i x => conj (g x) * firstOrderAction (a i) f x) hD
    (fun i => ((Complex.continuous_conj.comp g.continuous).mul
      (firstOrderAction_continuous_for_family ha i f)).aestronglyMeasurable) (fun i x => ?_)
  rw [norm_mul, Complex.norm_conj, mul_comm M]
  exact mul_le_mul_of_nonneg_left (hb i x) (norm_nonneg _)

end Burnett.Analysis.CarlesonEmbedding
