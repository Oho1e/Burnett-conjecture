import Burnett.Analysis.PrincipalEnergy.Quantization.BaseKernelDifference
import Burnett.Analysis.PrincipalEnergy.Quantization.SourceDifference

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel

/-- The target-variable estimate includes the change of the actual base
symbol, in addition to the reflected source-variable difference. -/
theorem exists_firstOrderLipschitzKernel_targetDifference {a : E → E → ℂ} (ha : FirstBaseFrequencyOrderOne a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : E → ℂ) (L : NNReal), LipschitzWith L r →
      ∀ (x x' y : E), x ≠ y → ‖x-x'‖ ≤ ‖x-y‖ / 2 →
        ‖coefficientKernel r (firstOrderKernel a) x y - coefficientKernel r (firstOrderKernel a) x' y‖ ≤
          (L : ℝ) * K * ‖x-x'‖ * (‖x-y‖ ^ 5)⁻¹ := by
  obtain ⟨p,C,hC,hP,hProf⟩ := exists_normalizedInverseProfiles ha.frequency
  obtain ⟨D,hD,hder⟩ := exists_firstOrderKernel_relativeDerivative_bound ha.frequency
  obtain ⟨B,hB,hbase⟩ := exists_firstOrderKernel_baseDifference ha
  refine ⟨34*C + 96*D + 32*B, by positivity, ?_⟩
  intro r L hr x x' y hxy hdistance
  let K := firstOrderKernel a
  let G (_ z : E) := K x (-z)
  have hG₀ (u z : E) (hz : z ≠ 0) : ‖G u z‖ ≤ (34*C) * (‖z‖^5)⁻¹ := by
    simpa only [G, K, norm_neg] using ((firstOrderKernel_size a p hP C hC hProf x (-z) (neg_ne_zero.mpr hz)).2 0).2
  have hG₁ (u z : E) (hz : z ≠ 0) : DifferentiableAt ℝ (G u) z ∧
      ‖fderiv ℝ (G u) z‖ ≤ D * (‖z‖^6)⁻¹ := by
    let N : E →L[ℝ] E := -ContinuousLinearMap.id ℝ E
    have hN : HasFDerivAt (fun q : E => -q) N z := N.hasFDerivAt
    obtain ⟨hKd,hKb⟩ := hder x (-z) (neg_ne_zero.mpr hz)
    have hF : HasFDerivAt (G u) ((fderiv ℝ (K x) (-z)).comp N) z := hKd.hasFDerivAt.comp z hN
    refine ⟨hF.differentiableAt, ?_⟩
    rw [hF.fderiv]
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have hNorm : ‖N‖ ≤ 1 := N.opNorm_le_bound zero_le_one (fun q => by
      change ‖-q‖ ≤ 1 * ‖q‖; rw [norm_neg, one_mul])
    exact (mul_le_of_le_one_right (norm_nonneg _) hNorm).trans (by simpa only [K, norm_neg] using hKb)
  have hFrozen := coefficientKernel_sourceDifference_le r hr G (34*C) D hD hG₀ hG₁ y x x' hxy.symm
    (by simpa only [norm_sub_rev y x] using hdistance)
  let S := (r x-r y) * K x (x-y) - (r x'-r y) * K x (x'-y)
  have hS : ‖S‖ ≤ (L : ℝ) * (34*C + 96*D) * ‖x-x'‖ * (‖x-y‖^5)⁻¹ := by
    have hFirst : -(y-x) = x-y := neg_sub y x
    have hSecond : -(y-x') = x'-y := neg_sub y x'
    have hSign : coefficientKernel r G y x - coefficientKernel r G y x' = -S := by
      simp only [coefficientKernel, G, hFirst, hSecond, S]
      ring
    rwa [hSign, norm_neg, norm_sub_rev y x] at hFrozen
  have hR : ‖x-y‖ ≤ ‖x'-y‖ + ‖x-x'‖ := by
    have t := norm_add_le (x'-y) (x-x')
    rwa [show x'-y+(x-x') = x-y by abel] at t
  have hSep : ‖x-y‖ / 2 ≤ ‖x'-y‖ := by linarith
  have hp := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have hp' := (half_pos hp).trans_le hSep
  have hLip : ‖r x'-r y‖ ≤ (L : ℝ)*‖x'-y‖ := by simpa only [dist_eq_norm] using hr.dist_le_mul x' y
  let T := (r x'-r y) * (K x (x'-y) - K x' (x'-y))
  have hT : ‖T‖ ≤ (L : ℝ) * (32*B) * ‖x-x'‖ * (‖x-y‖^5)⁻¹ := by
    have hInv : (‖x'-y‖^5)⁻¹ ≤ ((‖x-y‖ / 2)^5)⁻¹ :=
      (inv_le_inv₀ (pow_pos hp' _) (pow_pos (half_pos hp) _)).mpr (pow_le_pow_left₀ (by positivity) hSep _)
    change ‖(r x'-r y) * (K x (x'-y) - K x' (x'-y))‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ ((L : ℝ) * ‖x'-y‖) * (B * ‖x-x'‖ * (‖x'-y‖^6)⁻¹) :=
        mul_le_mul hLip (hbase x x' (x'-y) (norm_pos_iff.mp hp')) (norm_nonneg _) (by positivity)
      _ = (L : ℝ) * B * ‖x-x'‖ * (‖x'-y‖^5)⁻¹ := by
        field_simp [hp'.ne']
      _ ≤ (L : ℝ) * B * ‖x-x'‖ * ((‖x-y‖ / 2)^5)⁻¹ := mul_le_mul_of_nonneg_left hInv (by positivity)
      _ = _ := by
        field_simp [hp.ne']
        norm_num
  have hSplit : coefficientKernel r K x y - coefficientKernel r K x' y = S+T := by
    simp only [coefficientKernel, S, T]
    ring
  rw [hSplit]
  exact (norm_add_le _ _).trans ((add_le_add hS hT).trans_eq (by ring))

end Burnett.Analysis.FirstOrderDyadic
