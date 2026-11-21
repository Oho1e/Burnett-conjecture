import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderActionLimit

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform Topology

def expandingInput (χ : E → ℂ) (s : ℝ) (x : E) : ℂ := χ (s⁻¹ • x)

private theorem expandingInput_fourier (χ : E → ℂ) {s : ℝ} (hs : 0 < s) (η : E) :
    (𝓕 (expandingInput χ s)) η = s^4 • (𝓕 χ) (s • η) := by
  calc
    _ = (𝓕⁻ (expandingInput χ s)) (-η) := by
      rw [Real.fourierIntegralInv_eq_fourierIntegral_neg, neg_neg]
    _ = s^4 • (𝓕⁻ χ) (s • (-η)) := inverseFourier_dilation s hs χ (-η)
    _ = _ := by rw [smul_neg,Real.fourierIntegralInv_eq_fourierIntegral_neg,neg_neg]

private theorem inverseFourier_real_smul (c : ℝ) (f : E → ℂ) (x : E) :
    (𝓕⁻ (c • f)) x = c • (𝓕⁻ f) x := by
  simp only [Real.fourierIntegralInv_eq, Pi.smul_apply, smul_comm _ c, integral_smul]

/-- Actual positive-scale change of variables for the input tending to a
constant in the physical space. The x-variable of the symbol stays fixed. -/
theorem firstOrderHighAction_expandingInput {a : E → E → ℂ} (χ : E → ℂ)
    {s : ℝ} (hs : 0 < s) (x : E) :
    firstOrderHighAction a (expandingInput χ s) x =
      (𝓕⁻ (fun η => firstOrderHighSymbol a x (s⁻¹ • η) * (𝓕 χ) η)) (s⁻¹ • x) := by
  let q (η : E) := firstOrderHighSymbol a x (s⁻¹ • η) * (𝓕 χ) η
  have hf : (fun ξ => firstOrderHighSymbol a x ξ * (𝓕 (expandingInput χ s)) ξ) =
      s^4 • (fun ξ => q ((s⁻¹)⁻¹ • ξ)) := by
    funext ξ
    simp only [expandingInput_fourier χ hs, Pi.smul_apply, inv_inv, q, smul_smul,
      inv_mul_cancel₀ hs.ne', one_smul, mul_smul_comm]
  unfold firstOrderHighAction
  rw [hf, inverseFourier_real_smul, inverseFourier_dilation _ (inv_pos.mpr hs)]
  rw [smul_smul, inv_pow, mul_inv_cancel₀ (pow_ne_zero 4 hs.ne'), one_smul]

/-- For a first-order symbol with the fixed infrared cutoff, the high-frequency
operator applied to a fixed Schwartz input dilated to infinity tends to zero,
even when the base/evaluation point is allowed to vary with the scale. -/
theorem firstOrderHighAction_expandingInput_tendsto_zero (a : E → E → ℂ)
    (ha : FrequencyOrderOne a) (χ : SchwartzMap E ℂ) (x : ℕ → E) :
    Tendsto (fun n : ℕ => firstOrderHighAction a (expandingInput χ ((n:ℝ)+1)) (x n))
      atTop (𝓝 (0 : ℂ)) := by
  obtain ⟨M,hM,hA⟩ := ha.order 0
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let s (n : ℕ) : ℝ := n + 1
  have hs₁ (n : ℕ) : 1 ≤ s n := by unfold s; linarith [Nat.cast_nonneg (α := ℝ) n]
  have hs (n : ℕ) : 0 < s n := zero_lt_one.trans_le (hs₁ n)
  let env (η : E) := M * ((1 + ‖η‖) * ‖F η‖)
  let tail (n : ℕ) (η : E) := if s n < ‖η‖ then env η else 0
  have hEnv : Integrable env := by
    have h := F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)
    simpa only [env, add_mul, one_mul, pow_one] using h.const_mul M
  have hEnv₀ (η : E) : 0 ≤ env η := by dsimp [env]; positivity
  have hTailMeas (n : ℕ) : AEStronglyMeasurable (tail n) (volume : Measure E) :=
    (Measurable.ite (measurableSet_lt measurable_const measurable_norm)
      ((continuous_const.mul ((continuous_const.add continuous_norm).mul F.continuous.norm)).measurable)
      measurable_const).aestronglyMeasurable
  have hTailDom (n : ℕ) (η : E) : ‖tail n η‖ ≤ env η := by
    by_cases ht : s n < ‖η‖
    · simp only [tail, if_pos ht, Real.norm_of_nonneg (hEnv₀ η), le_refl]
    · simpa only [tail, if_neg ht, norm_zero] using hEnv₀ η
  have hCut : Tendsto (fun n : ℕ => ∫ η, tail n η) atTop (𝓝 0) := by
    rw [← integral_zero E ℝ]
    refine tendsto_integral_of_dominated_convergence env hTailMeas hEnv
      (fun n => Eventually.of_forall (hTailDom n)) (Eventually.of_forall fun η => ?_)
    apply tendsto_const_nhds.congr'
    obtain ⟨N,hN⟩ := exists_nat_ge ‖η‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have hnn : (N : ℝ) ≤ n := by exact_mod_cast hn
    have he : ¬ s n < ‖η‖ := by unfold s; linarith
    simp only [tail, if_neg he]
  have hActionBound (n : ℕ) :
      ‖firstOrderHighAction a (expandingInput χ (s n)) (x n)‖ ≤ ∫ η, tail n η := by
    rw [firstOrderHighAction_expandingInput (χ : E → ℂ) (hs n),Real.fourierIntegralInv_eq]
    refine (norm_integral_le_integral_norm _).trans (integral_mono_of_nonneg ?_ ?_ ?_)
    · exact Eventually.of_forall fun _ => norm_nonneg _
    · exact hEnv.mono' (hTailMeas n) (Eventually.of_forall (hTailDom n))
    · filter_upwards with η
      simp only [Circle.norm_smul]
      let ζ := (s n)⁻¹ • η
      have hζ : ‖ζ‖ = (s n)⁻¹ * ‖η‖ := by
        rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hs n).le)]
      by_cases hSmall : ‖η‖ ≤ s n
      · have hz : ‖ζ‖ ≤ 1 := by
          rw [hζ, mul_comm, ← div_eq_mul_inv]
          exact (div_le_one (hs n)).mpr hSmall
        simp [firstOrderHighSymbol, tail, if_neg (not_lt.mpr hSmall), radialCore_eq_one _ hz, ζ]
      · have hsInv : (s n)⁻¹ ≤ 1 := (inv_le_one₀ (hs n)).mpr (hs₁ n)
        have hnorm : ‖ζ‖ ≤ ‖η‖ := by
          rw [hζ]
          exact mul_le_of_le_one_left (norm_nonneg η) hsInv
        have hGrow : ‖a (x n) ζ‖ ≤ M * (1 + ‖ζ‖) := by
          simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hA (x n) ζ
        have hCore : ‖((1 - radialCore ζ : ℝ) : ℂ)‖ ≤ 1 := by
          rw [Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr (radialCore_le_one ζ))]
          linarith only [radialCore_nonneg ζ]
        change ‖firstOrderHighSymbol a (x n) ζ * F η‖ ≤ tail n η
        rw [show tail n η = env η by simp only [tail, if_pos (lt_of_not_ge hSmall)],
          firstOrderHighSymbol, norm_mul, norm_mul]
        calc
          _ ≤ ‖a (x n) ζ‖ * ‖F η‖ :=
            mul_le_mul_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) hCore) (norm_nonneg _)
          _ ≤ (M * (1 + ‖η‖)) * ‖F η‖ := mul_le_mul_of_nonneg_right
            (hGrow.trans (mul_le_mul_of_nonneg_left (add_le_add_left hnorm _) hM)) (norm_nonneg _)
          _ = env η := by unfold env; ring
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun _ => norm_nonneg _) hActionBound hCut

end Burnett.Analysis.FirstOrderDyadic
