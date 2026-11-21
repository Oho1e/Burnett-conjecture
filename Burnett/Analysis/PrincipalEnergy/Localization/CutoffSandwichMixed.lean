import Burnett.Analysis.PrincipalEnergy.Localization.CutoffSandwichMixedIntegrand

set_option autoImplicit false
set_option maxHeartbeats 3100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Metric Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff FourierTransform Topology

private theorem hasFDerivAt_cutoff_frequencyJet {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hSmooth : ContDiff ℝ ∞ (uncurry a))
    (χ : SchwartzMap Space ℂ) (n : ℕ) (x ξ : Space) :
    HasFDerivAt (fun y => iteratedFDeriv ℝ n (cutoffSandwichSymbol a χ y) ξ)
      (∫ η, fderiv ℝ (fun y => sandwichFrequencyFactor χ y η • iteratedFDeriv ℝ n (a y) (ξ + η)) x) x := by
  let V := ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ
  letI : NormedSpace ℂ V := ContinuousMultilinearMap.normedSpace'
  letI : NormedAddCommGroup (Space →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Space →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
  let u (η y : Space) : V := sandwichFrequencyFactor χ y η • iteratedFDeriv ℝ n (a y) (ξ + η)
  have phase : ContDiff ℝ ∞ (fun p : Space × Space => sandwichFrequencyFactor χ p.2 p.1) :=
    (contDiff_sandwichFrequencyFactor χ).comp (contDiff_snd.prodMk contDiff_fst)
  have displacement : ContDiff ℝ ∞ (fun p : Space × Space => ξ + p.1) :=
    (contDiff_const : ContDiff ℝ ∞ (fun _ : Space × Space => ξ)).add contDiff_fst
  have jet : ContDiff ℝ ∞ (fun p : Space × Space => iteratedFDeriv ℝ n (a p.2) (ξ + p.1)) :=
    (contDiff_symbol_frequencyJet hSmooth n).comp (contDiff_snd.prodMk displacement)
  have joint : ContDiff ℝ ∞ (uncurry u) := by
    have hB : IsBoundedBilinearMap ℝ (fun p : ℂ × V => p.1 • p.2) := isBoundedBilinearMap_smul
    change ContDiff ℝ ∞ ((fun q : ℂ × V => q.1 • q.2) ∘ fun p : Space × Space =>
      (sandwichFrequencyFactor χ p.2 p.1, iteratedFDeriv ℝ n (a p.2) (ξ + p.1)))
    exact hB.contDiff.comp (phase.prodMk jet)
  have measurable (y : Space) : AEStronglyMeasurable (fun η => u η y) (volume : Measure Space) := by
    have pair : Continuous (fun η : Space => (η, y)) := continuous_id.prodMk continuous_const
    exact (joint.continuous.comp pair).aestronglyMeasurable
  have diff (η y : Space) : DifferentiableAt ℝ (u η) y := by
    have pair : ContDiff ℝ ∞ (fun z : Space => (η, z)) :=
      contDiff_const.prodMk (contDiff_id : ContDiff ℝ ∞ (id : Space → Space))
    exact ((joint.comp pair).differentiable (by simp)) y
  have derivMeas : AEStronglyMeasurable (fun η => fderiv ℝ (u η) x) (volume : Measure Space) := by
    letI : SecondCountableTopologyEither Space (Space →L[ℝ] V) :=
      secondCountableTopologyEither_of_left _ _
    have h : Continuous (fun η => fderiv ℝ (u η) x) :=
      Continuous.fderiv_one (f := u) (g := fun _ => x) (joint.of_le (by simp)) continuous_const
    exact h.aestronglyMeasurable
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let S := SchwartzMap.seminorm ℝ 0 0 χ
  let W := 1 + ‖ξ‖
  have hW : 1 ≤ W := le_add_of_nonneg_right (norm_nonneg _)
  obtain ⟨A, hA, orderA⟩ := ha.frequency.order n
  have hInt : Integrable (fun η => u η x) (volume : Measure Space) := by
    refine ((integrable_schwartz_weighted F (n + 1)).const_mul (S * A * W)).mono'
      (measurable x) (Eventually.of_forall fun η => ?_)
    let v := iteratedFDeriv ℝ n (a x) (ξ + η)
    have hv : ‖v‖ ≤ A * W * (1 + ‖η‖)^(n + 1) := calc
      _ = ‖v‖ * 1 := (mul_one _).symm
      _ ≤ ‖v‖ * W^n := mul_le_mul_of_nonneg_left (one_le_pow₀ hW) (norm_nonneg _)
      _ ≤ _ := shifted_frequency_order_weight_le (fun y ζ => iteratedFDeriv ℝ n (a y) ζ)
        n hA orderA x ξ η
    have phaseNorm : ‖sandwichFrequencyFactor χ x η‖ ≤ S * ‖F η‖ :=
      (sandwichFrequencyFactor_base_controls χ x η).1
    change ‖sandwichFrequencyFactor χ x η • v‖ ≤ S * A * W * ((1 + ‖η‖)^(n + 1) * ‖F η‖)
    rw [norm_smul]
    exact (mul_le_mul phaseNorm hv (norm_nonneg _) ((norm_nonneg _).trans phaseNorm)).trans_eq (by ring)
  obtain ⟨C, _, orderD⟩ := exists_sandwichMixedIntegrand_derivative_bound ha χ n
  let w (η : Space) := (1 + ‖η‖)^(n + 2) * ‖F η‖
  have hD : ∀ᵐ η ∂(volume : Measure Space), ∀ y ∈ ball x 1, ‖fderiv ℝ (u η) y‖ ≤ (C * W) * w η :=
    Eventually.of_forall fun η y _ => calc
      _ = ‖fderiv ℝ (u η) y‖ * 1 := (mul_one _).symm
      _ ≤ ‖fderiv ℝ (u η) y‖ * W^n :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hW) (norm_nonneg _)
      _ ≤ _ := orderD y ξ η
  rw [show (fun y => iteratedFDeriv ℝ n (cutoffSandwichSymbol a χ y) ξ) =
      (fun y => ∫ η, u η y) from funext fun y => (cutoffSandwichSymbol_frequency_jets ha.frequency χ y).2 n ξ]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (show (0 : ℝ) < 1 from zero_lt_one)
    (Eventually.of_forall measurable) hInt derivMeas hD
    ((integrable_schwartz_weighted F (n + 2)).const_mul (C * W))
    (Eventually.of_forall fun η y _ => (diff η y).hasFDerivAt)

/-- The actual sandwich retains the mixed first-base order-one bound after
any number of frequency derivatives. -/
theorem cutoffSandwichSymbol_firstBaseFrequencyOrderOne {a : Space → Space → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) (hSmooth : ContDiff ℝ ∞ (uncurry a))
    (χ : SchwartzMap Space ℂ) : FirstBaseFrequencyOrderOne (cutoffSandwichSymbol a χ) := by
  refine ⟨cutoffSandwichSymbol_frequencyOrderOne ha.frequency χ,
    fun n ξ x => (hasFDerivAt_cutoff_frequencyJet ha hSmooth χ n x ξ).differentiableAt, ?_⟩
  intro n
  let V := ContinuousMultilinearMap ℝ (fun _ : Fin n => Space) ℂ
  letI : NormedAddCommGroup (Space →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
  letI : NormedSpace ℝ (Space →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
  obtain ⟨C, hC, orderD⟩ := exists_sandwichMixedIntegrand_derivative_bound ha χ n
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let w (η : Space) := (1 + ‖η‖)^(n + 2) * ‖F η‖
  have hW : Integrable w (volume : Measure Space) := integrable_schwartz_weighted F (n + 2)
  have hIW : 0 ≤ ∫ η, w η := integral_nonneg (fun η => by dsimp only [w]; positivity)
  refine ⟨C * (∫ η, w η), mul_nonneg hC hIW, fun x ξ => ?_⟩
  let D (η : Space) : Space →L[ℝ] V :=
    fderiv ℝ (fun y => sandwichFrequencyFactor χ y η • iteratedFDeriv ℝ n (a y) (ξ + η)) x
  let W := (1 + ‖ξ‖)^n
  have hW₀ : 0 ≤ W := by dsimp only [W]; positivity
  rw [(hasFDerivAt_cutoff_frequencyJet ha hSmooth χ n x ξ).fderiv]
  change ‖∫ η, D η‖ * W ≤ _
  calc
    _ = ‖W • (∫ η, D η)‖ := by rw [norm_smul, Real.norm_of_nonneg hW₀, mul_comm]
    _ = ‖∫ η, W • D η‖ := by rw [integral_smul]
    _ ≤ ∫ η, (C * (1 + ‖ξ‖)) * w η := by
      apply norm_integral_le_of_norm_le (hW.const_mul _)
      filter_upwards with η
      rw [norm_smul, Real.norm_of_nonneg hW₀, mul_comm]
      exact orderD x ξ η
    _ = _ := by rw [integral_const_mul]; ring

end Burnett.Analysis.CarlesonEmbedding
