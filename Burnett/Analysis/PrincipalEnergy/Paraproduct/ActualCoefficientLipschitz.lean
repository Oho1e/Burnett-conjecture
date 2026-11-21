import Burnett.Analysis.PrincipalEnergy.Paraproduct.ActualTwoWindowParaproduct

set_option autoImplicit false
set_option maxHeartbeats 3300000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Burnett.Analysis.FirstOrderDyadic
open scoped FourierTransform NNReal InnerProduct

private def phase (x ξ : Space) : ℂ :=
  Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)

private theorem phase_norm (x ξ : Space) : ‖phase x ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

private theorem phase_continuous (x : Space) : Continuous (phase x) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_const.mul (continuous_id.inner continuous_const))).mul continuous_const)

private theorem phase_diff_bound (x y ξ : Space) :
    ‖phase x ξ-phase y ξ‖ ≤ 2*Real.pi*‖ξ‖*‖x-y‖ := by
  let p (t : ℝ) := Complex.exp ((t:ℂ)*Complex.I)
  have hDer (t : ℝ) : HasDerivAt p (p t*Complex.I) t := by
    simpa only [p,id,Complex.ofReal_one,one_mul,mul_comm Complex.I] using
      (((hasDerivAt_id t).ofReal_comp).mul_const Complex.I).cexp
  have hpNorm (t : ℝ) : ‖p t‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hP (u v : ℝ) : ‖p u-p v‖ ≤ ‖u-v‖ := by
    have H := Convex.norm_image_sub_le_of_norm_deriv_le
      (fun t _ => (hDer t).differentiableAt)
      (fun t _ => show ‖deriv p t‖ ≤ (1:ℝ) by
        rw [(hDer t).deriv,norm_mul,hpNorm,Complex.norm_I,mul_one])
      convex_univ (mem_univ v) (mem_univ u)
    simpa only [one_mul] using H
  calc
    _ ≤ ‖2*Real.pi*inner ℝ ξ x-2*Real.pi*inner ℝ ξ y‖ := hP _ _
    _ = (2*Real.pi)*|inner ℝ ξ (x-y)| := by
      rw [← mul_sub,← inner_sub_right,Real.norm_eq_abs,abs_mul,
        abs_of_nonneg (mul_nonneg (by norm_num : 0≤(2:ℝ)) Real.pi_pos.le)]
    _ ≤ (2*Real.pi)*(‖ξ‖*‖x-y‖) := mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _)
      (mul_nonneg (by norm_num) Real.pi_pos.le)
    _ = _ := (mul_assoc _ _ _).symm

private theorem integrable_fourier_quadratic_moment (F : SchwartzMap Space ℂ) :
    Integrable (fun ξ : Space => (1+‖ξ‖)^2*‖F ξ‖) volume := by
  have hLinear := (F.integrable_pow_mul (volume : Measure Space) 1).const_mul 2
  have hQuadratic := F.integrable_pow_mul (volume : Measure Space) 2
  apply ((F.integrable.norm.add hLinear).add hQuadratic).congr
  filter_upwards with ξ
  simp only [Pi.add_apply,pow_one]
  ring

/-- The actual constant-test representative of the compact-base
commutator is Lipschitz for Schwartz r. Its Lipschitz constant may depend
on the weighted Fourier L¹ norm of r. -/
theorem exists_coefficientCommutatorConstant_lipschitz
    {a : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a)
    (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ)
    (hU : 0≤U) (hLip : LipschitzWith L r) (hV : ∀ x, ‖r x‖≤U) :
    ∃ M : NNReal, LipschitzWith M (coefficientCommutatorConstant a r) := by
  obtain ⟨D,hD,hBase⟩ := exists_frequencyDerivative_baseDifference_bound ha 0
  obtain ⟨A,hA,hFreq⟩ := ha.frequency.order 0
  have hA₁ (x ξ : Space) : ‖a x ξ‖ ≤ A*(1+‖ξ‖) := by
    simpa only [pow_zero,mul_one,norm_iteratedFDeriv_zero] using hFreq x ξ
  have hD₁ (x y ξ : Space) : ‖a x ξ-a y ξ‖ ≤ D*‖x-y‖*(1+‖ξ‖) := by
    have hEq : continuousMultilinearCurryFin0 ℝ Space ℂ
        (iteratedFDeriv ℝ 0 (a x) ξ-iteratedFDeriv ℝ 0 (a y) ξ) = a x ξ-a y ξ := by
      rw [map_sub]
      rfl
    rw [← hEq,LinearIsometryEquiv.norm_map]
    simpa only [pow_zero,mul_one] using hBase x y ξ
  let F := SchwartzMap.fourierTransformCLM ℂ r
  let W (ξ : Space) := 1+‖ξ‖
  let B (x ξ : Space) := phase x ξ*(a x ξ*F ξ)
  let I := ∫ ξ, W ξ^2*‖F ξ‖
  let K := D+2*Real.pi*A
  have hK : 0≤K := add_nonneg hD (mul_nonneg (by positivity) hA)
  have hI : 0≤I := integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (norm_nonneg _)
  have hW (ξ : Space) : 1≤W ξ := le_add_of_nonneg_right (norm_nonneg _)
  have hWS (ξ : Space) : W ξ ≤ W ξ^2 := le_self_pow₀ (hW ξ) (by decide)
  have hFT (x : Space) : firstOrderAction a r x = ∫ ξ, B x ξ := by
    rw [firstOrderAction,Real.fourierIntegralInv_eq']
    rfl
  have hB (x : Space) : Integrable (B x) volume := by
    apply ((integrable_fourier_quadratic_moment F).const_mul A).mono'
      ((phase_continuous x).mul ((ha.frequency.smooth x).continuous.mul F.continuous)).aestronglyMeasurable
    filter_upwards with ξ
    change ‖B x ξ‖ ≤ A*(W ξ^2*‖F ξ‖)
    simp only [B,norm_mul,phase_norm,one_mul]
    calc
      _ ≤ (A*W ξ)*‖F ξ‖ := mul_le_mul_of_nonneg_right (hA₁ x ξ) (norm_nonneg _)
      _ ≤ _ := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hWS ξ) hA) (norm_nonneg _)
  have hBNorm (x y : Space) :
      ‖firstOrderAction a r x-firstOrderAction a r y‖ ≤ (K*I)*‖x-y‖ := by
    have hIntegrand (ξ : Space) : ‖B x ξ-B y ξ‖ ≤ (K*‖x-y‖)*(W ξ^2*‖F ξ‖) := by
      rw [show B x ξ-B y ξ =
        (phase x ξ*(a x ξ-a y ξ)+(phase x ξ-phase y ξ)*a y ξ)*F ξ by dsimp only [B]; ring,norm_mul]
      rw [← mul_assoc (K*‖x-y‖) (W ξ^2) ‖F ξ‖]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg (F ξ))
      apply (norm_add_le _ _).trans
      rw [norm_mul,norm_mul,phase_norm,one_mul]
      have hTerm₁ : ‖a x ξ-a y ξ‖ ≤ (D*‖x-y‖)*W ξ^2 :=
        (hD₁ x y ξ).trans (mul_le_mul_of_nonneg_left (hWS ξ) (mul_nonneg hD (norm_nonneg _)))
      have hTerm₂ : ‖phase x ξ-phase y ξ‖*‖a y ξ‖ ≤ ((2*Real.pi*A)*‖x-y‖)*W ξ^2 := by
        calc
          _ ≤ (2*Real.pi*‖ξ‖*‖x-y‖)*(A*W ξ) :=
            mul_le_mul (phase_diff_bound x y ξ) (hA₁ y ξ) (norm_nonneg _) (by positivity)
          _ = ((2*Real.pi*A)*‖x-y‖)*(‖ξ‖*W ξ) := by ring
          _ ≤ _ := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [pow_two]
            exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one)
              (zero_le_one.trans (hW ξ))
      calc
        _ ≤ (D*‖x-y‖)*W ξ^2+((2*Real.pi*A)*‖x-y‖)*W ξ^2 := add_le_add hTerm₁ hTerm₂
        _ = _ := by dsimp only [K]; ring
    rw [hFT,hFT,← integral_sub (hB x) (hB y)]
    calc
      _ ≤ ∫ ξ, ‖B x ξ-B y ξ‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ ξ, (K*‖x-y‖)*(W ξ^2*‖F ξ‖) :=
        integral_mono (hB x |>.sub (hB y)).norm
          ((integrable_fourier_quadratic_moment F).const_mul _) hIntegrand
      _ = _ := by rw [integral_const_mul]; change K*‖x-y‖*I = K*I*‖x-y‖; ring
  let M := U*D+A*(L:ℝ)+K*I
  have hM : 0≤M := add_nonneg (add_nonneg (mul_nonneg hU hD) (mul_nonneg hA L.coe_nonneg)) (mul_nonneg hK hI)
  refine ⟨⟨M,hM⟩,lipschitzWith_iff_norm_sub_le.mpr fun x y => ?_⟩
  change ‖(r x*a x 0-firstOrderAction a r x)-(r y*a y 0-firstOrderAction a r y)‖ ≤ M*‖x-y‖
  rw [show (r x*a x 0-firstOrderAction a r x)-(r y*a y 0-firstOrderAction a r y) =
    (r x*(a x 0-a y 0)+(r x-r y)*a y 0)-(firstOrderAction a r x-firstOrderAction a r y) by ring]
  have hProd :
      ‖r x*(a x 0-a y 0)+(r x-r y)*a y 0‖ ≤ (U*D+A*(L:ℝ))*‖x-y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul,norm_mul]
    have hA₀ : ‖a y 0‖ ≤ A := by simpa only [norm_zero,add_zero,mul_one] using hA₁ y 0
    have hD₀ : ‖a x 0-a y 0‖ ≤ D*‖x-y‖ :=
      by simpa only [norm_zero,add_zero,mul_one] using hD₁ x y 0
    have hR₀ := lipschitzWith_iff_norm_sub_le.mp hLip x y
    calc
      _ ≤ U*(D*‖x-y‖)+((L:ℝ)*‖x-y‖)*A := add_le_add
        (mul_le_mul (hV x) hD₀ (norm_nonneg _) hU)
        (mul_le_mul hR₀ hA₀ (norm_nonneg _) (mul_nonneg L.coe_nonneg (norm_nonneg _)))
      _ = (U*D+A*(L:ℝ))*‖x-y‖ := by ring
  exact ((norm_sub_le _ _).trans (add_le_add hProd (hBNorm x y))).trans_eq (by
    dsimp only [M]
    ring)

end Burnett.Analysis.CarlesonEmbedding
