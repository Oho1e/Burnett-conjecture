import Burnett.Analysis.PrincipalEnergy.Quantization.PhysicalFrequencySplit
import Burnett.Analysis.PrincipalEnergy.Commutator.HighApproximateConstant

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Set Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform Topology

private theorem phase_zero_smul (z : ℂ) : (Real.fourierChar (0 : ℝ)) • z = z := by
  simp

private theorem expanded_fourier (χ : E → ℂ) {s : ℝ} (hs : 0 < s) (ξ : E) :
    (𝓕 (expandingInput χ s)) ξ = s^4 • (𝓕 χ) (s • ξ) := by
  calc
    _ = (𝓕⁻ (expandingInput χ s)) (-ξ) := by
      rw [Real.fourierIntegralInv_eq_fourierIntegral_neg,neg_neg]
    _ = s^4 • (𝓕⁻ χ) (s • (-ξ)) := inverseFourier_dilation s hs χ (-ξ)
    _ = _ := by rw [smul_neg,Real.fourierIntegralInv_eq_fourierIntegral_neg,neg_neg]

private theorem expanded_action (a : E → E → ℂ) (χ : E → ℂ) {s : ℝ} (hs : 0<s) (x : E) :
    firstOrderAction a (expandingInput χ s) x =
      (𝓕⁻ (fun η => a x (s⁻¹ • η) * (𝓕 χ) η)) (s⁻¹ • x) := by
  let q (η : E) := a x (s⁻¹ • η) * (𝓕 χ) η
  have h : (fun ξ => a x ξ * (𝓕 (expandingInput χ s)) ξ) =
      s^4 • (fun ξ => q ((s⁻¹)⁻¹ • ξ)) := by
    funext ξ
    simp only [expanded_fourier χ hs,Pi.smul_apply,inv_inv,q,smul_smul,
      inv_mul_cancel₀ hs.ne',one_smul,mul_smul_comm]
  have hMul (F : E → ℂ) : (𝓕⁻ (s^4 • F)) x = s^4 • (𝓕⁻ F) x := by
    simp only [Real.fourierIntegralInv_eq,Pi.smul_apply,smul_comm _ (s^4),integral_smul]
  unfold firstOrderAction
  rw [h,hMul,inverseFourier_dilation _ (inv_pos.mpr hs),smul_smul,inv_pow,
    mul_inv_cancel₀ (pow_ne_zero 4 hs.ne'),one_smul]

/-- The full physical operator applied to genuine expanding Schwartz tests
converges at each fixed point to its symbol at zero times the central value. -/
theorem firstOrderAction_expandingInput_tendsto {a : E → E → ℂ} (ha : FrequencyOrderOne a)
    (χ : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n : ℕ => firstOrderAction a (expandingInput χ ((n:ℝ)+1)) x)
      atTop (𝓝 (a x 0 * χ 0)) := by
  obtain ⟨D,hD,hGrowth⟩ := ha.order 0
  let s (n : ℕ) : ℝ := n+1
  have hs₁ (n : ℕ) : 1 ≤ s n := by unfold s; linarith [Nat.cast_nonneg (α:=ℝ) n]
  have hs (n : ℕ) : 0 < s n := zero_lt_one.trans_le (hs₁ n)
  have hScale : Tendsto (fun n => (s n)⁻¹) atTop (𝓝 0) := by
    simpa only [s,one_div] using tendsto_one_div_add_atTop_nhds_zero_nat
  let F := SchwartzMap.fourierTransformCLM ℂ χ
  let G (n : ℕ) (η : E) := (Real.fourierChar (inner ℝ η ((s n)⁻¹ • x))) •
    (a x ((s n)⁻¹ • η)*F η)
  let J (η : E) := D*((1+‖η‖)*‖F η‖)
  have hI : Integrable J := by
    simpa only [J,add_mul,one_mul,pow_one] using
      (F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)).const_mul D
  have hMeas (n : ℕ) : AEStronglyMeasurable (G n) (volume : Measure E) :=
    ((Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)).smul
      (((ha.smooth x).continuous.comp (continuous_const.smul continuous_id)).mul F.continuous)).aestronglyMeasurable
  have hDom (n : ℕ) (η : E) : ‖G n η‖ ≤ J η := by
    change ‖(Real.fourierChar (inner ℝ η ((s n)⁻¹ • x))) •
      (a x ((s n)⁻¹ • η) * F η)‖ ≤ _
    rw [Circle.norm_smul,norm_mul]
    have hh : ‖(s n)⁻¹ • η‖ ≤ ‖η‖ := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hs n).le)]
      exact mul_le_of_le_one_left (norm_nonneg _) ((inv_le_one₀ (hs n)).mpr (hs₁ n))
    have ha' : ‖a x ((s n)⁻¹ • η)‖ ≤ D*(1+‖(s n)⁻¹ • η‖) := by
      simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hGrowth x ((s n)⁻¹ • η)
    exact (mul_le_mul_of_nonneg_right (ha'.trans
      (mul_le_mul_of_nonneg_left (add_le_add_left hh 1) hD)) (norm_nonneg _)).trans_eq (by unfold J; ring)
  have hS (η : E) : Tendsto (fun n => (s n)⁻¹ • η) atTop (𝓝 (0 : E)) := by
    simpa only [zero_smul] using hScale.smul_const η
  have hLim (η : E) : Tendsto (fun n => G n η) atTop (𝓝 (a x 0 * F η)) := by
    have hPhaseC : Continuous (fun p : E => Real.fourierChar (inner ℝ η p)) :=
      Real.continuous_fourierChar.comp (continuous_const.inner continuous_id)
    have hp := hPhaseC.continuousAt.tendsto.comp (hS x)
    have hB := (ha.smooth x).continuous.continuousAt.tendsto.comp (hS η)
    have hF : Tendsto (fun _ : ℕ => F η) atTop (𝓝 (F η)) := tendsto_const_nhds
    simpa only [Function.comp_apply,G,inner_zero_right,phase_zero_smul] using
      hp.smul (hB.mul hF)
  have hRec : (∫ η : E, F η) = χ 0 := by
    have hχ := congrFun (χ.continuous.fourier_inversion χ.integrable F.integrable) 0
    simpa only [Real.fourierIntegralInv_eq,inner_zero_right,phase_zero_smul] using hχ
  have hIntegral := tendsto_integral_of_dominated_convergence J hMeas hI
    (fun n => Eventually.of_forall (hDom n)) (Eventually.of_forall hLim)
  rw [integral_const_mul,hRec] at hIntegral
  refine hIntegral.congr' (Eventually.of_forall fun n => ?_)
  change (∫ η, G n η) = firstOrderAction a (expandingInput χ (s n)) x
  rw [expanded_action a (χ : E → ℂ) (hs n),Real.fourierIntegralInv_eq]
  rfl

/-- The actual (M_r B-BM_r) on the expanding tests has the explicit
pointwise constant-input limit for a compactly supported coefficient. -/
theorem firstOrderCoefficientCommutator_expandingInput_tendsto {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (r χ : SchwartzMap E ℂ)
    (hr : HasCompactSupport (r : E → ℂ))
    (hχ : ∀ y : E, ‖y‖ ≤ 1 → χ y = 1) (x : E) :
    Tendsto (fun n : ℕ =>
      r x * firstOrderAction a (expandingInput χ ((n:ℝ)+1)) x -
        firstOrderAction a (fun y => r y * expandingInput χ ((n:ℝ)+1) y) x)
      atTop (𝓝 (r x * a x 0 - firstOrderAction a r x)) := by
  have hχ0 := hχ (0:E) (by simp)
  have hPart := firstOrderAction_expandingInput_tendsto ha χ x
  rw [hχ0,mul_one] at hPart
  obtain ⟨R,hR⟩ := hr.bddAbove_image continuous_norm.continuousOn
  obtain ⟨N,hN⟩ := exists_nat_ge R
  have hEq : (fun n : ℕ => fun y => r y * expandingInput χ ((n:ℝ)+1) y) =ᶠ[atTop] (fun _ => (r : E → ℂ)) := by
    filter_upwards [eventually_ge_atTop N] with n hnn
    funext y
    by_cases hy : r y = 0
    · simp only [hy,zero_mul]
    have hs : 0 < (n:ℝ)+1 := by positivity
    have hz : ‖y‖ ≤ (n:ℝ)+1 := by
      have hSize := hR (mem_image_of_mem norm (subset_closure hy))
      have hNatural : (N : ℝ) ≤ n := by exact_mod_cast hnn
      linarith
    have hNorm : ‖(((n:ℝ)+1)⁻¹) • y‖ ≤ 1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hs.le),← div_eq_inv_mul]
      exact (div_le_one hs).mpr hz
    rw [expandingInput,hχ _ hNorm,mul_one]
  have hSecond : Tendsto (fun _ : ℕ => firstOrderAction a r x) atTop
      (𝓝 (firstOrderAction a r x)) := tendsto_const_nhds
  have hRx : Tendsto (fun _ : ℕ => r x) atTop (𝓝 (r x)) := tendsto_const_nhds
  have hMain := (hRx.mul hPart).sub hSecond
  refine hMain.congr' (hEq.mono fun n hn => ?_)
  change r x * firstOrderAction a (expandingInput χ ((n:ℝ)+1)) x -
    firstOrderAction a r x = r x * firstOrderAction a (expandingInput χ ((n:ℝ)+1)) x -
    firstOrderAction a (fun y => r y * expandingInput χ ((n:ℝ)+1) y) x
  change (fun y => r y * expandingInput χ ((n:ℝ)+1) y) = (r : E → ℂ) at hn
  rw [hn]

end Burnett.Analysis.FirstOrderDyadic
