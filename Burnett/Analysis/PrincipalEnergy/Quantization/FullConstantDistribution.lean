import Burnett.Analysis.PrincipalEnergy.Quantization.FullUniformExpanded

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Set Burnett.Microlocal.AngularDyadicKernel
open scoped Topology ContDiff ComplexConjugate

private def expandingCompactSchwartz (χ : SchwartzMap E ℂ) (hχ : HasCompactSupport (χ : E → ℂ))
    {s : ℝ} (hs : 0 < s) : SchwartzMap E ℂ := by
  let e : E ≃ₜ E := Homeomorph.smulOfNeZero (s⁻¹) (inv_ne_zero hs.ne')
  have hc : HasCompactSupport (fun x : E => χ (s⁻¹ • x)) := hχ.comp_homeomorph e
  have hSmooth : ContDiff ℝ ∞ (χ : E → ℂ) := χ.smooth _
  exact hc.toSchwartzMap (hSmooth.comp (contDiff_const.smul contDiff_id))

/-- For compactly based symbols and compactly supported coefficient r, the actual
constant-input limit can be tested against any complex Schwartz test. -/
theorem coefficientCommutator_expandingInput_tested {a : E → E → ℂ}
    (ha : FrequencyOrderOne a) (hBase : CompactBaseOrderOne a) (hCont : Continuous (Function.uncurry a))
    (r χ v : SchwartzMap E ℂ) (hr : HasCompactSupport (r : E → ℂ)) (hχ : HasCompactSupport (χ : E → ℂ))
    (hOne : ∀ x : E, ‖x‖ ≤ 1 → χ x = 1) :
    Tendsto (fun n : ℕ => ∫ x, conj (v x) *
      (r x*firstOrderAction a (expandingInput χ ((n:ℝ)+1)) x -
        firstOrderAction a (fun y => r y*expandingInput χ ((n:ℝ)+1) y) x))
      atTop (𝓝 (∫ x, conj (v x)*(r x*a x 0 - firstOrderAction a r x))) := by
  let s (n : ℕ) : ℝ := n+1
  have hs (n : ℕ) : 1 ≤ s n := by unfold s; linarith [Nat.cast_nonneg (α:=ℝ) n]
  let f (n : ℕ) := expandingCompactSchwartz χ hχ (zero_lt_one.trans_le (hs n))
  let A (n : ℕ) (x : E) := firstOrderAction a (f n) x
  let B (x : E) := firstOrderAction a r x
  let P (n : ℕ) (x : E) := conj (v x) * (r x*A n x - B x)
  obtain ⟨M,hM,hBound⟩ := exists_firstOrderAction_expandingInput_uniform_bound ha χ
  let R := SchwartzMap.seminorm ℝ 0 0 r
  let V := SchwartzMap.seminorm ℝ 0 0 v
  have hR : 0 ≤ R := apply_nonneg _ _
  have hV : 0 ≤ V := apply_nonneg _ _
  have hBi : Integrable B := firstOrderAction_integrable_of_compactBase hBase hCont r
  let D (x : E) := (R*M)*‖v x‖+V*‖B x‖
  have hD : Integrable D := (v.integrable.norm.const_mul _).add (hBi.norm.const_mul _)
  have hMeas (n : ℕ) : AEStronglyMeasurable (P n) (volume : Measure E) := by
    have hAi := firstOrderAction_integrable_of_compactBase hBase hCont (f n)
    exact v.continuous.aestronglyMeasurable.star.mul
      ((r.continuous.aestronglyMeasurable.mul hAi.aestronglyMeasurable).sub hBi.aestronglyMeasurable)
  have hDom (n : ℕ) (x : E) : ‖P n x‖ ≤ D x := by
    have hRa : ‖r x*A n x‖ ≤ R*M := by
      rw [norm_mul]
      exact mul_le_mul (SchwartzMap.norm_le_seminorm ℝ r x) (hBound _ (hs n) x) (norm_nonneg _) hR
    calc
      _ ≤ ‖v x‖ * (‖r x*A n x‖+‖B x‖) := by
        dsimp only [P]; rw [norm_mul,Complex.norm_conj]
        exact mul_le_mul_of_nonneg_left (norm_sub_le _ _) (norm_nonneg _)
      _ ≤ ‖v x‖ * (R*M+‖B x‖) := mul_le_mul_of_nonneg_left (add_le_add_right hRa _) (norm_nonneg _)
      _ ≤ _ := by
        dsimp only [D]
        rw [mul_add,mul_comm ‖v x‖ (R*M)]
        exact add_le_add_left (mul_le_mul_of_nonneg_right (SchwartzMap.norm_le_seminorm ℝ v x) (norm_nonneg _)) _
  have hLim (x : E) : Tendsto (fun n => P n x) atTop
      (𝓝 (conj (v x)*(r x*a x 0-B x))) := by
    have h := firstOrderAction_expandingInput_tendsto ha χ x
    rw [hOne 0 (by simp),mul_one] at h
    exact (((h.const_mul (r x)).sub_const (B x)).const_mul (conj (v x)))
  have hMain := tendsto_integral_of_dominated_convergence D hMeas hD
    (fun n => Eventually.of_forall (hDom n)) (Eventually.of_forall hLim)
  obtain ⟨R₀,hR₀⟩ := hr.bddAbove_image continuous_norm.continuousOn
  obtain ⟨N,hN⟩ := exists_nat_ge R₀
  apply hMain.congr'
  filter_upwards [eventually_ge_atTop N] with n hn
  have hEq : (fun y => r y * expandingInput χ (s n) y) = (r : E → ℂ) := by
    funext y
    by_cases hy : r y = 0
    · simp only [hy,zero_mul]
    have hS : 0 < s n := zero_lt_one.trans_le (hs n)
    have hY : ‖y‖ ≤ s n := by
      have hc := hR₀ (mem_image_of_mem norm (subset_closure hy))
      have hNat : (N : ℝ) ≤ n := by exact_mod_cast hn
      dsimp [s]
      linarith
    have hV₁ : ‖(s n)⁻¹ • y‖ ≤ 1 := by
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le),← div_eq_inv_mul]
      exact (div_le_one hS).mpr hY
    rw [expandingInput,hOne _ hV₁,mul_one]
  change (∫ x, P n x) = ∫ x, conj (v x) * (r x*firstOrderAction a (expandingInput χ (s n)) x -
    firstOrderAction a (fun y => r y*expandingInput χ (s n) y) x)
  rw [hEq]
  rfl

end Burnett.Analysis.FirstOrderDyadic
