import Burnett.Analysis.PrincipalEnergy.Quantization.BaseDerivative

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform Topology

private def relativeSymbol (a : E → E → ℂ) (p : E × E) (ξ : E) : ℂ :=
  ‖p.1-p.2‖⁻¹ • (a p.1 ξ - a p.2 ξ)

private theorem relativeSymbol_order {a : E → E → ℂ} (ha : FirstBaseFrequencyOrderOne a) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ξ,
      ‖iteratedFDeriv ℝ n (relativeSymbol a p) ξ‖ * (1 + ‖ξ‖)^n ≤ C * (1 + ‖ξ‖) := by
  obtain ⟨C,hC,hC'⟩ := exists_frequencyDerivative_baseDifference_bound ha n
  refine ⟨C,hC,?_⟩
  intro ⟨x,y⟩ ξ
  have hle : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hx : ContDiffAt ℝ n (a x) ξ := (ha.frequency.smooth x).contDiffAt.of_le hle
  have hy : ContDiffAt ℝ n (a y) ξ := (ha.frequency.smooth y).contDiffAt.of_le hle
  have hNeg : ContDiffAt ℝ n (-(a y)) ξ := hy.neg
  have hAdd : ContDiffAt ℝ n (a x + -(a y)) ξ := hx.add hNeg
  change ‖iteratedFDeriv ℝ n (‖x-y‖⁻¹ • (a x + -(a y))) ξ‖ * (1 + ‖ξ‖)^n ≤ _
  rw [iteratedFDeriv_const_smul_apply hAdd, iteratedFDeriv_add_apply hx hNeg,
    iteratedFDeriv_neg_apply, ← sub_eq_add_neg, norm_smul, Real.norm_of_nonneg (by positivity)]
  rw [mul_assoc]
  refine (mul_le_mul_of_nonneg_left (hC' x y ξ) (by positivity)).trans ?_
  by_cases he : ‖x-y‖ = 0
  · simp only [he, inv_zero, mul_zero, zero_mul]
    positivity
  · rw [show ‖x-y‖⁻¹ * (C * ‖x-y‖ * (1 + ‖ξ‖)) = C * (1 + ‖ξ‖) by field_simp]

private theorem annulusFrequency_integrable (a : E → E → ℂ) (ha : FrequencyOrderOne a) (x : E) (j : ℕ) :
    Integrable (normalizedFirstOrderAnnulus a x j) (volume : Measure E) := by
  have hc : HasCompactSupport (normalizedFirstOrderAnnulus a x j) := by
    apply (isCompact_closedBall (0 : E) 4).of_isClosed_subset isClosed_closure
    apply closure_minimal _ Metric.isClosed_closedBall
    intro ξ hξ
    by_contra hFar
    have h' : 4 < ‖ξ‖ := lt_of_not_ge (by simpa only [Metric.mem_closedBall, dist_zero_right] using hFar)
    exact hξ (by simp [normalizedFirstOrderAnnulus, annulus_eq_zero_far ξ h'.le])
  apply Continuous.integrable_of_hasCompactSupport _ hc
  exact ((Complex.continuous_ofReal.comp annulus_contDiff.continuous).mul
    ((ha.smooth x).continuous.comp (continuous_const.smul continuous_id))).const_smul _

private theorem annular_difference (a : E → E → ℂ) (ha : FrequencyOrderOne a) (x y : E) (j : ℕ)
    (p : SchwartzMap E ℂ) (hp : (p : E → ℂ) = 𝓕⁻ (normalizedFirstOrderAnnulus (fun _ => relativeSymbol a (x,y)) 0 j))
    (z : E) : firstOrderAnnularKernel a x j z - firstOrderAnnularKernel a y j z =
      ‖x-y‖ • (dyadicScale j ^ 5 • p (dyadicScale j • z)) := by
  by_cases hxy : x = y
  · simp [hxy]
  have hd : ‖x-y‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hxy)
  let s := dyadicScale j
  let A := normalizedFirstOrderAnnulus a x j
  let B := normalizedFirstOrderAnnulus a y j
  have hEq : normalizedFirstOrderAnnulus (fun _ => relativeSymbol a (x,y)) 0 j = ‖x-y‖⁻¹ • (A-B) := by
    funext ξ
    change s⁻¹ • (annulus ξ : ℂ) • (‖x-y‖⁻¹ • (a x (s • ξ) - a y (s • ξ))) =
      ‖x-y‖⁻¹ • (s⁻¹ • (annulus ξ : ℂ) • a x (s • ξ) - s⁻¹ • (annulus ξ : ℂ) • a y (s • ξ))
    rw [smul_comm (annulus ξ : ℂ) (‖x-y‖⁻¹), smul_comm (s⁻¹) (‖x-y‖⁻¹), smul_sub, smul_sub]
  have hInv : ∀ v, (𝓕⁻ (‖x-y‖⁻¹ • (A-B))) v = ‖x-y‖⁻¹ • ((𝓕⁻ A) v - (𝓕⁻ B) v) := by
    intro v
    simp only [Real.fourierIntegralInv_eq, Pi.smul_apply, Pi.sub_apply]
    have hCommuting : (fun ξ : E => Real.fourierChar (inner ℝ ξ v) • (‖x-y‖⁻¹ • (A ξ-B ξ))) =
        (fun ξ : E => ‖x-y‖⁻¹ • (Real.fourierChar (inner ℝ ξ v) • A ξ - Real.fourierChar (inner ℝ ξ v) • B ξ)) := by
      funext ξ
      rw [smul_comm (Real.fourierChar _) _, smul_sub (Real.fourierChar _)]
    rw [hCommuting, integral_smul]
    have hChar : Continuous (fun ξ : E => Real.fourierChar (inner ℝ ξ v)) :=
      Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
    have hInt (M : E → ℂ) (h : Integrable M (volume : Measure E)) :
        Integrable (fun ξ => Real.fourierChar (inner ℝ ξ v) • M ξ) (volume : Measure E) :=
      h.mono (hChar.aestronglyMeasurable.smul h.1) (Filter.Eventually.of_forall fun ξ => by rw [Circle.norm_smul])
    rw [integral_sub (hInt A (annulusFrequency_integrable a ha x j)) (hInt B (annulusFrequency_integrable a ha y j))]
  rw [firstOrderAnnularKernel_eq_scaled, firstOrderAnnularKernel_eq_scaled, ← smul_sub, hp, hEq, hInv]
  rw [smul_comm (‖x-y‖) (s ^ 5), smul_smul (‖x-y‖) (‖x-y‖⁻¹), mul_inv_cancel₀ hd, one_smul]

/-- The full nonhomogeneous base variation uses the integrable tail power
available from one further Fourier moment on the normalized profiles. -/
theorem exists_firstOrderKernel_baseDifference {a : E → E → ℂ} (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x y z, z ≠ 0 →
      ‖firstOrderKernel a x z - firstOrderKernel a y z‖ ≤ C * ‖x-y‖ * (‖z‖ ^ 6)⁻¹ := by
  obtain ⟨p,C,hC,hp,hP⟩ := exists_uniformFamilyInverseProfiles (relativeSymbol a)
    (fun q => ((ha.frequency.smooth q.1).sub (ha.frequency.smooth q.2)).const_smul _) (relativeSymbol_order ha)
  obtain ⟨p₀,B,hB,hp₀,hP₀⟩ := exists_normalizedInverseProfiles ha.frequency
  refine ⟨2*C, by positivity, ?_⟩
  intro x y z hz
  let v (j : ℕ) := firstOrderAnnularKernel a x j z - firstOrderAnnularKernel a y j z
  let M := C * ‖x-y‖ * (‖z‖ ^ 6)⁻¹
  have hF (j : ℕ) : ‖v j‖ ≤ M * (1/2 : ℝ)^j := by
    change ‖firstOrderAnnularKernel a x j z - firstOrderAnnularKernel a y j z‖ ≤ _
    rw [annular_difference a ha.frequency x y j (p (x,y) j) (hp (x,y) j) z, norm_smul,
      Real.norm_of_nonneg (norm_nonneg _)]
    have hs : 0 ≤ (dyadicScale j)⁻¹ := by unfold dyadicScale; positivity
    calc
      _ ≤ ‖x-y‖ * (SchwartzMap.seminorm ℝ 6 0 (p (x,y) j) * (dyadicScale j)⁻¹ * (‖z‖^6)⁻¹) :=
        mul_le_mul_of_nonneg_left (scaledSchwartz_high_bound (p (x,y) j) 5 j z hz) (norm_nonneg _)
      _ ≤ ‖x-y‖ * (C * (dyadicScale j)⁻¹ * (‖z‖^6)⁻¹) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hP (x,y) j) hs) (by positivity)) (norm_nonneg _)
      _ = _ := by unfold M; rw [dyadicScale, ← inv_pow, ← one_div]; ring
  have hGeom : ‖(1/2 : ℝ)‖ < 1 := by norm_num
  have hS : Summable (fun j => M * (1/2 : ℝ)^j) := (summable_geometric_of_norm_lt_one hGeom).mul_left M
  have hSv : Summable (fun j => ‖v j‖) := Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hF hS
  have hK (u : E) : Summable (fun j => firstOrderAnnularKernel a u j z) :=
    (firstOrderKernel_size a p₀ hp₀ B hB hP₀ u z hz).1.of_norm
  calc
    _ = ‖∑' j, v j‖ := by rw [firstOrderKernel, firstOrderKernel, ← (hK x).tsum_sub (hK y)]
    _ ≤ ∑' j, ‖v j‖ := norm_tsum_le_tsum_norm hSv
    _ ≤ ∑' j, M * (1/2 : ℝ)^j := hSv.tsum_le_tsum hF hS
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hGeom]; norm_num [M]; ring

end Burnett.Analysis.FirstOrderDyadic
