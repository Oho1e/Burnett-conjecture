import Burnett.Analysis.PrincipalEnergy.Commutator.CompactBaseCommutatorL2

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform

/-- Complex linear combinations of the actual symbols, in the same left quantization. -/
def combineSymbols (c d : ℂ) (a b : Space → Space → ℂ) (x ξ : Space) : ℂ :=
  c • a x ξ + d • b x ξ

private theorem weighted_norm_combination {F : Type*} [SeminormedAddCommGroup F] [NormedSpace ℂ F]
    (c d : ℂ) (u v : F) {t W A B : ℝ} (ht : 0 ≤ t)
    (hu : ‖u‖ * t ≤ A * W) (hv : ‖v‖ * t ≤ B * W) :
    ‖c • u + d • v‖ * t ≤ (‖c‖ * A + ‖d‖ * B) * W := by
  calc
    _ ≤ (‖c‖ * ‖u‖ + ‖d‖ * ‖v‖) * t := by
      apply mul_le_mul_of_nonneg_right _ ht
      simpa only [norm_smul] using norm_add_le (c • u) (d • v)
    _ = ‖c‖ * (‖u‖ * t) + ‖d‖ * (‖v‖ * t) := by ring
    _ ≤ ‖c‖ * (A * W) + ‖d‖ * (B * W) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hv (norm_nonneg _))
    _ = _ := by ring

private theorem iteratedFDeriv_combination (c d : ℂ) {u v : Space → ℂ} {n : ℕ} {x : Space}
    (hu : ContDiffAt ℝ n u x) (hv : ContDiffAt ℝ n v x) :
    iteratedFDeriv ℝ n (c • u + d • v) x =
      c • iteratedFDeriv ℝ n u x + d • iteratedFDeriv ℝ n v x := by
  change iteratedFDeriv ℝ n ((fun y => c • u y) + fun y => d • v y) x = _
  rw [iteratedFDeriv_add_apply (hu.const_smul c) (hv.const_smul d),
    iteratedFDeriv_const_smul_apply' (a := c) hu, iteratedFDeriv_const_smul_apply' (a := d) hv]

theorem combineSymbols_frequencyOrderOne {a b : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hb : FrequencyOrderOne b) (c d : ℂ) :
    FrequencyOrderOne (combineSymbols c d a b) := by
  refine ⟨fun x => ((ha.smooth x).const_smul c).add ((hb.smooth x).const_smul d), ?_⟩
  intro n
  obtain ⟨A, hA, boundA⟩ := ha.order n
  obtain ⟨B, hB, boundB⟩ := hb.order n
  refine ⟨‖c‖ * A + ‖d‖ * B, by positivity, fun x ξ => ?_⟩
  have lhs : combineSymbols c d a b x = c • a x + d • b x := rfl
  rw [lhs, iteratedFDeriv_combination c d
    ((ha.smooth x).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hb.smooth x).contDiffAt.of_le (by exact_mod_cast le_top))]
  exact weighted_norm_combination c d (iteratedFDeriv ℝ n (a x) ξ)
    (iteratedFDeriv ℝ n (b x) ξ) (by positivity) (boundA x ξ) (boundB x ξ)

private theorem frequencyDerivative_combineSymbols {a b : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hb : FrequencyOrderOne b) (c d : ℂ) (n : ℕ) (ξ : Space) :
    (fun x => iteratedFDeriv ℝ n (combineSymbols c d a b x) ξ) =
      (fun x => c • iteratedFDeriv ℝ n (a x) ξ + d • iteratedFDeriv ℝ n (b x) ξ) := by
  funext x
  change iteratedFDeriv ℝ n (c • a x + d • b x) ξ = _
  exact iteratedFDeriv_combination c d
    ((ha.smooth x).contDiffAt.of_le (by exact_mod_cast le_top))
    ((hb.smooth x).contDiffAt.of_le (by exact_mod_cast le_top))

theorem combineSymbols_firstBaseFrequencyOrderOne {a b : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hb : FirstBaseFrequencyOrderOne b) (c d : ℂ) :
    FirstBaseFrequencyOrderOne (combineSymbols c d a b) := by
  refine ⟨combineSymbols_frequencyOrderOne ha.frequency hb.frequency c d, ?_, ?_⟩
  · intro n ξ
    rw [frequencyDerivative_combineSymbols ha.frequency hb.frequency]
    exact ((ha.baseDiff n ξ).const_smul c).add ((hb.baseDiff n ξ).const_smul d)
  · intro n
    obtain ⟨A, hA, boundA⟩ := ha.order n
    obtain ⟨B, hB, boundB⟩ := hb.order n
    refine ⟨‖c‖ * A + ‖d‖ * B, by positivity, fun x ξ => ?_⟩
    rw [frequencyDerivative_combineSymbols ha.frequency hb.frequency]
    let u := fun y => iteratedFDeriv ℝ n (a y) ξ
    let v := fun y => iteratedFDeriv ℝ n (b y) ξ
    have hu : DifferentiableAt ℝ u x := (ha.baseDiff n ξ).differentiableAt
    have hv : DifferentiableAt ℝ v x := (hb.baseDiff n ξ).differentiableAt
    change ‖fderiv ℝ (c • u + d • v) x‖ * (1 + ‖ξ‖)^n ≤ _
    rw [fderiv_add (hu.const_smul c) (hv.const_smul d),
      fderiv_const_smul hu c, fderiv_const_smul hv d]
    exact weighted_norm_combination c d (fderiv ℝ u x) (fderiv ℝ v x)
      (by positivity) (boundA x ξ) (boundB x ξ)

theorem combineSymbols_compactBaseOrderOne {a b : Space → Space → ℂ}
    (ha : CompactBaseOrderOne a) (hb : CompactBaseOrderOne b) (c d : ℂ) :
    CompactBaseOrderOne (combineSymbols c d a b) := by
  refine ⟨?_, fun ξ => ((ha.smooth ξ).const_smul c).add ((hb.smooth ξ).const_smul d), ?_⟩
  · obtain ⟨K, hK, hSuppK⟩ := ha.support
    obtain ⟨L, hL, hSuppL⟩ := hb.support
    refine ⟨K ∪ L, hK.union hL, fun ξ => closure_minimal (fun x hx => ?_) (hK.union hL).isClosed⟩
    by_contra hh
    have hax : a x ξ = 0 := by
      by_contra hax
      exact hh (Or.inl (hSuppK ξ (subset_closure hax)))
    have hbx : b x ξ = 0 := by
      by_contra hbx
      exact hh (Or.inr (hSuppL ξ (subset_closure hbx)))
    apply hx
    change c • a x ξ + d • b x ξ = 0
    simp only [hax, hbx, smul_zero, add_zero]
  · intro n
    obtain ⟨A, hA, boundA⟩ := ha.order n
    obtain ⟨B, hB, boundB⟩ := hb.order n
    refine ⟨‖c‖ * A + ‖d‖ * B, by positivity, fun x ξ => ?_⟩
    change ‖iteratedFDeriv ℝ n (c • (fun y => a y ξ) + d • (fun y => b y ξ)) x‖ ≤ _
    rw [iteratedFDeriv_combination c d
      ((ha.smooth ξ).contDiffAt.of_le (by exact_mod_cast le_top))
      ((hb.smooth ξ).contDiffAt.of_le (by exact_mod_cast le_top))]
    have hFa := boundA x ξ
    have hFb := boundB x ξ
    rw [← mul_one ‖iteratedFDeriv ℝ n (fun y => a y ξ) x‖] at hFa
    rw [← mul_one ‖iteratedFDeriv ℝ n (fun y => b y ξ) x‖] at hFb
    simpa only [mul_one] using weighted_norm_combination c d _ _ zero_le_one hFa hFb

private theorem symbolAction_integrand_integrable {a : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (f : SchwartzMap Space ℂ) (x : Space) :
    Integrable (fun ξ => (Real.fourierChar (inner ℝ ξ x)) • (a x ξ * 𝓕 (f : Space → ℂ) ξ)) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  obtain ⟨A, _, hb⟩ := ha.order 0
  have hBound (ξ : Space) : ‖a x ξ‖ ≤ A * (1 + ‖ξ‖) := by
    simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hb x ξ
  have hI := (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure Space) 1)).const_mul A
  have hPhase : Continuous (fun ξ => Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  apply hI.mono' (hPhase.smul ((ha.smooth x).continuous.mul F.continuous)).aestronglyMeasurable
  filter_upwards with ξ
  change ‖Real.fourierChar (inner ℝ ξ x) • (a x ξ * F ξ)‖ ≤ A * (‖F ξ‖ + ‖ξ‖^1 * ‖F ξ‖)
  rw [Circle.norm_smul, norm_mul, pow_one, ← one_add_mul]
  exact (mul_le_mul_of_nonneg_right (hBound ξ) (norm_nonneg _)).trans_eq (mul_assoc _ _ _)

/-- The sums and complex factors in the symbol give the identical
pointwise sum of the two physical operator actions. -/
theorem firstOrderAction_combineSymbols {a b : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hb : FrequencyOrderOne b)
    (c d : ℂ) (f : SchwartzMap Space ℂ) (x : Space) :
    firstOrderAction (combineSymbols c d a b) f x =
      c * firstOrderAction a f x + d * firstOrderAction b f x := by
  simp only [firstOrderAction, Real.fourierIntegralInv_eq]
  let P (ξ : Space) := Real.fourierChar (inner ℝ ξ x)
  let F (ξ : Space) := 𝓕 (f : Space → ℂ) ξ
  let A (ξ : Space) := P ξ • (a x ξ * F ξ)
  let B (ξ : Space) := P ξ • (b x ξ * F ξ)
  have hEq : (fun ξ => P ξ • (combineSymbols c d a b x ξ * F ξ)) =
      fun ξ => c * A ξ + d * B ξ := by
    funext ξ
    simp only [A, B, combineSymbols, smul_eq_mul, Circle.smul_def]
    ring
  change (∫ ξ, P ξ • (combineSymbols c d a b x ξ * F ξ)) = c * (∫ ξ, A ξ) + d * (∫ ξ, B ξ)
  rw [hEq, integral_add ((symbolAction_integrand_integrable ha f x).const_mul c)
    ((symbolAction_integrand_integrable hb f x).const_mul d), integral_const_mul, integral_const_mul]

theorem actualCoefficientCommutator_combineSymbols {a b : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hb : FrequencyOrderOne b)
    (c d : ℂ) (r f : SchwartzMap Space ℂ) (x : Space) :
    actualCoefficientCommutator (combineSymbols c d a b) r f x =
      c * actualCoefficientCommutator a r f x + d * actualCoefficientCommutator b r f x := by
  simp only [actualCoefficientCommutator, firstOrderAction_combineSymbols ha hb]
  ring

end Burnett.Analysis.CarlesonEmbedding
