import Burnett.Analysis.PrincipalEnergy.Freezing.SeparatedModeEnergy
import Burnett.Analysis.PrincipalEnergy.Freezing.RadianSkewDifferentiation
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Module

set_option autoImplicit false
set_option maxHeartbeats 1850000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff BigOperators FourierTransform RealInnerProductSpace

private theorem homogeneous_mode_bound (b : E → ℝ) (D : ℝ) (hD : 0 ≤ D)
    (hom : ∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ)
    (sphereBound : ∀ ξ ∈ sphere (0 : E) 1, ‖b ξ‖ ≤ D) (ξ : E) :
    ‖b (tau • ξ)‖ ≤ D * (tau * ‖ξ‖) := by
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  by_cases eq : ξ = 0
  · have b0 := hom 2 (by norm_num) (0 : E)
    simp only [smul_zero] at b0
    have hz : b 0 = 0 := by linarith
    rw [eq, smul_zero, hz, norm_zero]
    exact mul_nonneg hD (mul_nonneg hτ.le (norm_nonneg _))
  let y := ‖ξ‖⁻¹ • ξ
  have hξ : 0 < ‖ξ‖ := norm_pos_iff.mpr eq
  have hy : y ∈ sphere (0 : E) 1 := by
    simpa only [mem_sphere, dist_zero_right, y] using norm_smul_inv_norm (𝕜 := ℝ) eq
  have scaled : tau • ξ = (tau * ‖ξ‖) • y := by
    dsimp only [y]
    rw [smul_smul, mul_assoc, mul_inv_cancel₀ hξ.ne', mul_one]
  rw [scaled, hom _ (mul_pos hτ hξ), norm_mul, Real.norm_of_nonneg (mul_nonneg hτ.le hξ.le)]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (sphereBound y hy) (mul_nonneg hτ.le hξ.le)

/-- The actual left operator uses the same physical symbol section in the
radian Fourier integral. Dominated convergence identifies its value from
the pointwise symbol series and the summable real mode weights. -/
theorem hasSum_left_radian_skew_modes {I : Type*} [Countable I]
    (g : I → Fin 2 → ℝ) (b : I → Fin 2 → E → ℝ) (D : I → Fin 2 → ℝ)
    (smooth : ∀ k j, ContDiffOn ℝ ∞ (b k j) {ξ | ξ ≠ 0})
    (hom : ∀ k j (t : ℝ), 0 < t → ∀ ξ, b k j (t • ξ) = t * b k j ξ)
    (nonneg : ∀ k j, 0 ≤ D k j)
    (jet₀ : ∀ k j ξ, ξ ∈ sphere (0 : E) 1 → ‖b k j ξ‖ ≤ D k j)
    (s : E → ℝ) (pointwise : ∀ ξ, HasSum (fun k => ∑ j : Fin 2, g k j * b k j ξ) (s ξ))
    (absoluteWeight : Summable (fun k : I => ∑ j : Fin 2, ‖g k j‖ * D k j))
    (u : SchwartzMap E ℂ) (x : E) :
    HasSum (fun k : I => ∑ j : Fin 2, (g k j : ℂ) * radianSkewAction (b k j) u x)
      (radianSkewAction s u x) := by
  classical
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let phase (ξ : E) := Complex.exp ((↑(tau * inner ℝ ξ x) : ℂ) * Complex.I)
  let transfer (ξ : E) := phase ξ * (-Complex.I) * U ξ
  let W (k : I) := ∑ j : Fin 2, ‖g k j‖ * D k j
  let V (ξ : E) := tau * (‖ξ‖ * ‖U ξ‖)
  let F (k : I) (ξ : E) := transfer ξ * (↑(∑ j : Fin 2, g k j * b k j (tau • ξ)) : ℂ)
  let total (ξ : E) := transfer ξ * (s (tau • ξ) : ℂ)
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hPhase : Continuous phase := by
    have hInner : Continuous (fun ξ : E => inner ℝ ξ x) := continuous_id.inner continuous_const
    exact Complex.continuous_exp.comp
      ((Complex.continuous_ofReal.comp (continuous_const.mul hInner)).mul continuous_const)
  have hTransfer : Continuous transfer := (hPhase.mul continuous_const).mul U.continuous
  have hNorm (ξ : E) : ‖transfer ξ‖ = ‖U ξ‖ := by
    simp only [transfer, norm_mul, phase, Complex.norm_exp_ofReal_mul_I, norm_neg, Complex.norm_I, one_mul]
  have hBMeas (k : I) (j : Fin 2) : Measurable (fun ξ : E => b k j (tau • ξ)) :=
    (measurable_of_continuousOn_compl_singleton 0 (smooth k j).continuousOn).comp
      (continuous_const.smul continuous_id).measurable
  have hMeas (k : I) : AEStronglyMeasurable (F k) volume := by
    have hCoeffs : Measurable (fun ξ : E => ∑ j : Fin 2, g k j * b k j (tau • ξ)) :=
      Finset.measurable_fun_sum _ (fun j _ => measurable_const.mul (hBMeas k j))
    exact (hTransfer.measurable.mul (Complex.continuous_ofReal.measurable.comp hCoeffs)).aestronglyMeasurable
  have hDom (k : I) (ξ : E) : ‖F k ξ‖ ≤ W k * V ξ := by
    rw [show ‖F k ξ‖ = ‖U ξ‖ * ‖∑ j : Fin 2, g k j * b k j (tau • ξ)‖ by
      simp only [F, norm_mul, hNorm, Complex.norm_real]]
    have finiteSum : ‖∑ j : Fin 2, g k j * b k j (tau • ξ)‖ ≤ W k * (tau * ‖ξ‖) := by
      change _ ≤ (∑ j : Fin 2, ‖g k j‖ * D k j) * (tau * ‖ξ‖)
      rw [Finset.sum_mul]
      apply norm_sum_le_of_le
      intro j _
      rw [norm_mul]
      refine (mul_le_mul_of_nonneg_left
        (homogeneous_mode_bound (b k j) (D k j) (nonneg k j) (hom k j) (jet₀ k j) ξ)
        (norm_nonneg _)).trans_eq ?_
      ring
    exact (mul_le_mul_of_nonneg_left finiteSum (norm_nonneg _)).trans_eq (by dsimp only [V]; ring)
  have hPoint (ξ : E) : HasSum (fun k => F k ξ) (total ξ) :=
    (((pointwise (tau • ξ)).mapL Complex.ofRealCLM).mul_left (transfer ξ))
  have hV : Integrable V := by
    simpa only [V, pow_one] using (U.integrable_pow_mul volume 1).const_mul tau
  have hDomInt : Integrable (fun ξ => ∑' k, W k * V ξ) := by
    simp_rw [tsum_mul_right]
    exact hV.const_mul _
  have sum := hasSum_integral_of_dominated_convergence (μ := volume) (fun k ξ => W k * V ξ)
    hMeas (fun k => Eventually.of_forall (hDom k))
    (Eventually.of_forall fun ξ => absoluteWeight.mul_right (V ξ)) hDomInt (Eventually.of_forall hPoint)
  have modeIntegral (r : ℝ) (q : E → ℝ) :
      (∫ ξ, transfer ξ * (↑(r * q (tau • ξ)) : ℂ)) =
        (r : ℂ) * radianSkewAction q u x := by
    rw [radianSkewAction, ← radianActionSpectrum_inverse, Real.fourierIntegralInv_eq']
    rw [← integral_const_mul, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with ξ
    simp only [transfer, phase, radianActionSpectrum, Complex.ofReal_mul, smul_eq_mul]
    rw [show U ξ = 𝓕 (u : E → ℂ) ξ from rfl]
    ring
  have modeEq (k : I) : (∫ ξ, F k ξ) = ∑ j : Fin 2, (g k j : ℂ) * radianSkewAction (b k j) u x := by
    have int (j : Fin 2) : Integrable (fun ξ => transfer ξ * (↑(g k j * b k j (tau • ξ)) : ℂ)) := by
      refine (hV.const_mul (‖g k j‖ * D k j)).mono'
        ((hTransfer.measurable.mul (Complex.continuous_ofReal.measurable.comp
          (measurable_const.mul (hBMeas k j)))).aestronglyMeasurable) ?_
      filter_upwards with ξ
      rw [norm_mul, hNorm, Complex.norm_real, norm_mul]
      exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (homogeneous_mode_bound (b k j) (D k j) (nonneg k j) (hom k j) (jet₀ k j) ξ)
        (norm_nonneg _)) (norm_nonneg _)).trans_eq (by dsimp only [V]; ring)
    have eq : F k = (fun ξ => ∑ j : Fin 2, transfer ξ * (↑(g k j * b k j (tau • ξ)) : ℂ)) := by
      funext ξ
      simp only [F, Complex.ofReal_sum, Finset.mul_sum]
    rw [eq, integral_finset_sum Finset.univ (fun j _ => int j)]
    exact Finset.sum_congr rfl fun j _ => modeIntegral (g k j) (b k j)
  simp_rw [modeEq] at sum
  have hTotal : (∫ ξ, total ξ) = radianSkewAction s u x := by
    simpa only [one_mul, Complex.ofReal_one] using modeIntegral 1 s
  exact hTotal ▸ sum

/-- The exact pointwise difference between symmetrization and left multiplication. -/
theorem separated_skew_left_difference (f : SchwartzMap E ℂ) (b : E → ℝ)
    (u : SchwartzMap E ℂ) (x : E) :
    separatedSkewAction f b u x - f x * radianSkewAction b u x =
      (radianSkewAction b (energyProduct f u) x - f x * radianSkewAction b u x) / 2 := by
  unfold separatedSkewAction
  ring

end Burnett.A03
