import Burnett.Analysis.PrincipalEnergy.Commutator.HighApproximateConstant
import Burnett.Analysis.PrincipalEnergy.Commutator.HighOffSupportAction
import Burnett.Analysis.PrincipalEnergy.Commutator.RenormalizedKernel
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Set Metric Burnett.Microlocal.AngularDyadicKernel
open scoped Topology ContDiff

private def expandingCompactSchwartz (χ : SchwartzMap E ℂ) (hχ : HasCompactSupport (χ : E → ℂ))
    {s : ℝ} (hs : 0 < s) : SchwartzMap E ℂ := by
  let e : E ≃ₜ E := Homeomorph.smulOfNeZero (s⁻¹) (inv_ne_zero hs.ne')
  have hc : HasCompactSupport (fun x : E => χ (s⁻¹ • x)) := hχ.comp_homeomorph e
  have hSmooth : ContDiff ℝ ∞ (χ : E → ℂ) := χ.smooth _
  exact hc.toSchwartzMap (hSmooth.comp (contDiff_const.smul contDiff_id))

private theorem inverse_fifth_le_shifted {r δ : ℝ} (hδ : 0 < δ) (hr : δ ≤ r) :
    (r^5)⁻¹ ≤ (1+δ⁻¹)^5 * ((1+r)^5)⁻¹ := by
  have hR : 0 < r := hδ.trans_le hr
  have hz : 1 ≤ δ⁻¹ * r := by
    rw [← div_eq_inv_mul]
    exact (le_div_iff₀ hδ).mpr (by simpa using hr)
  have hm : 1+r ≤ (1+δ⁻¹)*r := by nlinarith
  rw [← div_eq_mul_inv, ← one_div]
  apply (div_le_div_iff₀ (pow_pos hR _) (pow_pos (by positivity : 0 < 1+r) _)).mpr
  rw [one_mul, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) hm _

private theorem shifted_inverse_fifth_integrable (x : E) :
    Integrable (fun y : E => ((1+‖x-y‖)^5)⁻¹) := by
  have hi : Integrable (fun y : E => ((1+‖y‖)^5)⁻¹) := by
    have hdim : (Module.finrank ℝ E : ℝ) < 5 := by norm_num [finrank_euclideanSpace_fin]
    apply (integrable_one_add_norm (μ := (volume : Measure E)) hdim).congr
    filter_upwards with y
    rw [Real.rpow_neg (by positivity)]
    norm_num [Real.rpow_natCast]
  exact ((volume : Measure E).measurePreserving_sub_left x).integrable_comp_of_integrable hi

/-- If the input is locally constant at the evaluation point, the actual
high-frequency action equals the integral against that constant-subtracted
input. The subtraction at infinity is justified by genuine expanding tests. -/
theorem firstOrderHighAction_eq_kernel_sub_constant {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (g χ : SchwartzMap E ℂ)
    (hχC : HasCompactSupport (χ : E → ℂ)) (hχOne : ∀ y : E, ‖y‖ ≤ 1 → χ y = 1)
    (hχBound : ∀ y : E, ‖χ y‖ ≤ 1)
    (x : E) (c : ℂ) (δ : ℝ) (hδ : 0 < δ) (hNear : ∀ y ∈ ball x δ, g y = c) :
    Integrable (fun y => firstOrderKernel a x (x-y) * (g y-c)) ∧
      firstOrderHighAction a g x = ∫ y, firstOrderKernel a x (x-y) * (g y-c) := by
  obtain ⟨N,hN⟩ := exists_nat_ge (‖x‖+δ)
  let s (n : ℕ) : ℝ := ((n+N : ℕ) : ℝ) + 1
  have hs (n : ℕ) : 0 < s n := by unfold s; positivity
  let χn (n : ℕ) : SchwartzMap E ℂ := expandingCompactSchwartz χ hχC (hs n)
  have hχNorm (n : ℕ) (y : E) : ‖χn n y‖ ≤ 1 := hχBound ((s n)⁻¹ • y)
  have hPlateau (n : ℕ) (y : E) (hy : ‖y‖ ≤ s n) : χn n y = 1 := by
    apply hχOne
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (hs n).le), ← div_eq_inv_mul]
    exact (div_le_one (hs n)).mpr hy
  let g' (n : ℕ) := g - c • χn n
  have hg' (n : ℕ) (y : E) (hy : y ∈ ball x δ) : g' n y = 0 := by
    have hDist : ‖y-x‖ < δ := by simpa only [mem_ball,dist_eq_norm] using hy
    have hSize : ‖y‖ ≤ ‖y-x‖ + ‖x‖ := by simpa using norm_add_le (y-x) x
    have hR : (N : ℝ) ≤ s n := by
      have ha : N ≤ n+N := Nat.le_add_left _ _
      unfold s
      have hb : (N : ℝ) ≤ ((n+N : ℕ) : ℝ) := by exact_mod_cast ha
      linarith
    have hSmall : ‖y‖ ≤ s n := by linarith
    simp only [g', SchwartzMap.sub_apply, SchwartzMap.smul_apply, hNear y hy, hPlateau n y hSmall,
      smul_eq_mul, mul_one, sub_self]
  have hxSupport (n : ℕ) : x ∉ tsupport (g' n : E → ℂ) := by
    have hsupp : Function.support (g' n : E → ℂ) ⊆ (ball x δ)ᶜ :=
      fun y hy h => hy (hg' n y h)
    exact fun h => (closure_minimal hsupp isOpen_ball.isClosed_compl h) (mem_ball_self hδ)
  obtain ⟨p,C,hC,hp,hBound⟩ := exists_normalizedInverseProfiles ha
  let K (y : E) := firstOrderKernel a x (x-y)
  let Ebound (y : E) := (34*C*(1+δ⁻¹)^5 * (SchwartzMap.seminorm ℝ 0 0 g + ‖c‖)) *
    ((1+‖x-y‖)^5)⁻¹
  have hBound₁ : Integrable Ebound := (shifted_inverse_fifth_integrable x).const_mul _
  have hDom (n : ℕ) (y : E) : ‖K y * g' n y‖ ≤ Ebound y := by
    by_cases hy : y ∈ ball x δ
    · rw [hg' n y hy, mul_zero, norm_zero]
      unfold Ebound
      positivity
    have hDist : δ ≤ ‖x-y‖ := by
      simpa only [mem_ball,dist_comm y x,dist_eq_norm,not_lt] using hy
    have hNev : x-y ≠ 0 := norm_pos_iff.mp (hδ.trans_le hDist)
    have hK := ((firstOrderKernel_size a p hp C hC hBound x (x-y) hNev).2 0).2
    have hG : ‖g' n y‖ ≤ SchwartzMap.seminorm ℝ 0 0 g + ‖c‖ := by
      change ‖g y - c • χn n y‖ ≤ _
      refine (norm_sub_le _ _).trans (add_le_add (SchwartzMap.norm_le_seminorm ℝ g y) ?_)
      rw [norm_smul]
      exact mul_le_of_le_one_right (norm_nonneg _) (hχNorm n y)
    rw [norm_mul]
    refine (mul_le_mul hK hG (norm_nonneg _) (by positivity)).trans ?_
    calc
      _ ≤ (34*C*((1+δ⁻¹)^5 * ((1+‖x-y‖)^5)⁻¹)) *
          (SchwartzMap.seminorm ℝ 0 0 g + ‖c‖) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (inverse_fifth_le_shifted hδ hDist) (by positivity)) (by positivity)
      _ = _ := by unfold Ebound; ring
  have hConv (y : E) : Tendsto (fun n => K y * g' n y) atTop (𝓝 (K y * (g y-c))) := by
    apply tendsto_const_nhds.congr'
    obtain ⟨M,hM⟩ := exists_nat_ge ‖y‖
    filter_upwards [eventually_ge_atTop M] with n hn
    have hnn : (M : ℝ) ≤ ((n+N : ℕ) : ℝ) := by exact_mod_cast (hn.trans (Nat.le_add_right n N))
    have he : ‖y‖ ≤ s n := by unfold s; linarith
    simp only [g',SchwartzMap.sub_apply,SchwartzMap.smul_apply,smul_eq_mul,hPlateau n y he,mul_one]
  have hM (n : ℕ) : AEStronglyMeasurable (fun y => K y * g' n y) volume :=
    (firstOrderHighAction_offSupport ha (g' n) x (hxSupport n)).1.aestronglyMeasurable
  have hOut : Integrable (fun y => K y * (g y-c)) :=
    hBound₁.mono' (aestronglyMeasurable_of_tendsto_ae atTop hM (Eventually.of_forall hConv))
      (Eventually.of_forall fun y => le_of_tendsto (hConv y).norm (Eventually.of_forall fun n => hDom n y))
  have hIntegrals := tendsto_integral_of_dominated_convergence Ebound hM hBound₁
    (fun n => Eventually.of_forall (hDom n)) (Eventually.of_forall hConv)
  have hShift : Tendsto (fun n : ℕ => n+N) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_add_right n N) tendsto_id
  have hConst := (firstOrderHighAction_expandingInput_tendsto_zero a ha χ (fun _ => x)).comp hShift
  have hFreq : Tendsto (fun n : ℕ => firstOrderHighAction a (g' n) x)
      atTop (𝓝 (firstOrderHighAction a g x)) := by
    simp only [g',firstOrderHighAction_sub_smul a ha x]
    have hZero : Tendsto (fun n : ℕ => firstOrderHighAction a (χn n) x) atTop (𝓝 (0 : ℂ)) := by
      change Tendsto (fun n : ℕ => firstOrderHighAction a (expandingInput χ (s n)) x) atTop (𝓝 (0 : ℂ))
      exact hConst
    simpa only [mul_zero, sub_zero] using (tendsto_const_nhds.sub (tendsto_const_nhds.mul hZero))
  refine ⟨hOut,tendsto_nhds_unique hFreq ?_⟩
  exact hIntegrals.congr' (Eventually.of_forall fun n =>
    (firstOrderHighAction_offSupport ha (g' n) x (hxSupport n)).2.symm)

end Burnett.Analysis.FirstOrderDyadic
