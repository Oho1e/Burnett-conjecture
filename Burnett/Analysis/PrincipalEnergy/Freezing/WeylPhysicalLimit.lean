import Burnett.Analysis.PrincipalEnergy.Freezing.WeylPhysicalKernel
import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 2600000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform Topology

private theorem one_weighted_transform_integrable (f : SchwartzMap E ℂ) :
    Integrable (fun ξ => (1 + ‖ξ‖) * ‖𝓕 (f : E → ℂ) ξ‖) := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have h := F.integrable.norm.add (F.integrable_pow_mul volume 1)
  exact h.congr (Eventually.of_forall fun ξ => by
    change ‖F ξ‖ + ‖ξ‖ ^ 1 * ‖F ξ‖ = (1 + ‖ξ‖) * ‖F ξ‖
    rw [pow_one, add_mul, one_mul])

/-- Quantization is continuous on genuine Schwartz inputs under a uniform
linear frequency majorant and pointwise convergence of the symbols. -/
theorem separated_radian_quantization_tendsto (σ : ℝ) (bₙ : ℕ → E → ℝ)
    (b : E → ℝ) (bnM : ∀ n, Measurable (bₙ n)) (bM : Measurable b)
    (A : ℝ) (A0 : 0 ≤ A)
    (bnB : ∀ n ξ, ‖bₙ n ξ‖ ≤ A * (1 + ‖ξ‖)) (bB : ∀ ξ, ‖b ξ‖ ≤ A * (1 + ‖ξ‖))
    (conv : ∀ ξ, Tendsto (fun n => bₙ n ξ) atTop (𝓝 (b ξ)))
    (f u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => separatedRadianQuantization σ (bₙ n) f u x) atTop
      (𝓝 (separatedRadianQuantization σ b f u x)) := by
  obtain ⟨C, C0, weight⟩ := slanted_radian_symbol_growth σ (fun ξ => A * (1 + ‖ξ‖)) A A0
    (fun ξ => by rw [Real.norm_of_nonneg (mul_nonneg A0 (by positivity))])
  let N (n : ℕ) := slantedRadianSymbol σ (bₙ n)
  let M := slantedRadianSymbol σ b
  have nGrow (n : ℕ) (η ξ : E) : ‖N n (η, tau • ξ)‖ ≤ C * (1 + ‖η‖) * (1 + ‖ξ‖) :=
    (bnB n _).trans ((le_abs_self _).trans (weight η ξ))
  have mGrow (η ξ : E) : ‖M (η, tau • ξ)‖ ≤ C * (1 + ‖η‖) * (1 + ‖ξ‖) :=
    (bB _).trans ((le_abs_self _).trans (weight η ξ))
  have measN (n : ℕ) : Measurable (N n) := slanted_radian_symbol_measurable σ _ (bnM n)
  have measM : Measurable M := slanted_radian_symbol_measurable σ b bM
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let U := SchwartzMap.fourierTransformCLM ℂ u
  let P (a : E × E → ℝ) (η ξ : E) :=
    patchFourierPhase ξ x * ((a (η, tau • ξ) : ℂ) * U ξ)
  let j (ξ : E) := (1 + ‖ξ‖) * ‖U ξ‖
  have Ji : Integrable j := one_weighted_transform_integrable u
  have phase (ξ : E) : ‖patchFourierPhase ξ x‖ = 1 := patch_fourier_phase_norm ξ x
  let args : E → E × E := fun ξ => (ξ,x)
  have argsC : Continuous args := continuous_id.prodMk continuous_const
  have phaseC : Continuous (fun ξ : E => patchFourierPhase ξ x) := by
    change Continuous ((fun z : E × E => patchFourierPhase z.1 z.2) ∘ args)
    exact patch_fourier_phase_continuous.comp argsC
  have pM (a : E × E → ℝ) (ha : Measurable a) (η : E) : Measurable (P a η) := by
    have argC : Continuous (fun ξ : E => (η, tau • ξ)) :=
      continuous_const.prodMk (continuous_const.smul continuous_id)
    exact phaseC.measurable.mul ((Complex.continuous_ofReal.measurable.comp (ha.comp argC.measurable)).mul
      U.continuous.measurable)
  have pB (n : ℕ) (η ξ : E) : ‖P (N n) η ξ‖ ≤ (C * (1 + ‖η‖)) * j ξ := by
    simp only [P, phase, norm_mul, one_mul, Complex.norm_real, j]
    exact (mul_le_mul_of_nonneg_right (nGrow n η ξ) (norm_nonneg _)).trans_eq (mul_assoc ..)
  let R (a : E × E → ℝ) (η : E) := radianAction (fun ξ => a (η, ξ)) u x
  have re (a : E × E → ℝ) (η : E) : R a η = ∫ ξ, P a η ξ := radian_action_fourier_integral _ _ _
  have inner (η : E) : Tendsto (fun n => R (N n) η) atTop (𝓝 (R M η)) := by
    simp_rw [re]
    refine tendsto_integral_of_dominated_convergence (fun ξ => (C * (1 + ‖η‖)) * j ξ)
      (fun n => (pM (N n) (measN n) η).aestronglyMeasurable)
      (Ji.const_mul _) (fun n => Eventually.of_forall (pB n η)) ?_
    apply Eventually.of_forall
    intro ξ
    have l : Tendsto (fun n => (N n (η,tau • ξ) : ℂ)) atTop (𝓝 (M (η,tau • ξ) : ℂ)) :=
      (Complex.continuous_ofReal.tendsto _).comp (conv _)
    exact tendsto_const_nhds.mul (l.mul tendsto_const_nhds)
  let G (a : E × E → ℝ) (η : E) := (patchFourierPhase η x * F η) * R a η
  have gM (a : E × E → ℝ) (ha : Measurable a) : Measurable (G a) := by
    let atX : E → E × E := fun η => (η, x)
    let h : E × E → ℂ := fun z => radianAction (fun ξ => a (z.1, ξ)) u z.2
    have haX : Measurable atX := measurable_id.prodMk measurable_const
    have hh : Measurable h := radian_action_varying_measurable a ha u
    have rM : Measurable (R a) := by
      change Measurable (h ∘ atX)
      exact hh.comp haX
    exact (phaseC.measurable.mul F.continuous.measurable).mul rM
  have gB (n : ℕ) (η : E) :
      ‖G (N n) η‖ ≤ (C * (∫ ξ, j ξ)) * ((1 + ‖η‖) * ‖F η‖) := by
    simp only [G, norm_mul, phase, one_mul, re]
    have e := norm_integral_le_of_norm_le (Ji.const_mul (C * (1 + ‖η‖))) (Eventually.of_forall (pB n η))
    rw [integral_const_mul] at e
    exact (mul_le_mul_of_nonneg_left e (norm_nonneg _)).trans_eq (by ring)
  have eq (a : E × E → ℝ) (ha : Measurable a) (ga : RadianAverageGrowth a) :
      radianFourierAverage a f u x = ∫ η, G a η := radian_fourier_average_eq_integral a ha ga f u x
  change Tendsto (fun n => radianFourierAverage (N n) f u x) atTop (𝓝 (radianFourierAverage M f u x))
  simp_rw [eq (N _) (measN _) ⟨C,C0,nGrow _⟩, eq M measM ⟨C,C0,mGrow⟩]
  exact tendsto_integral_of_dominated_convergence _ (fun n => (gM _ (measN n)).aestronglyMeasurable)
    ((one_weighted_transform_integrable f).const_mul (C * ∫ ξ, j ξ))
    (fun n => Eventually.of_forall (gB n))
    (Eventually.of_forall fun η => tendsto_const_nhds.mul (inner η))

private theorem normalized_radial_cutoff_compact (b : E → ℝ) (n : ℕ) :
    HasCompactSupport (fun ξ : E => ((mikhlinBall (((n : ℝ)+1)⁻¹ • ξ) * b (tau • ξ) : ℝ) : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2 * ((n : ℝ)+1)))
  intro ξ hx
  by_contra outside
  have h : 2 * ((n : ℝ)+1) < ‖ξ‖ := by
    simpa only [mem_closedBall, dist_zero_right, not_le] using outside
  have far : 2 ≤ dist (((n : ℝ)+1)⁻¹ • ξ) (0 : E) := by
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
    exact (le_div_iff₀ (by positivity)).mpr h.le
  exact hx (by simp only [mikhlinBall.zero_of_le_dist far, zero_mul, Complex.ofReal_zero])

/-- The smooth symbol is exhausted by explicit normalized frequency cutoffs. -/
def normalizedRadianCutoffProfile (b : E → ℝ) (hb : ContDiff ℝ ∞ b) (n : ℕ) : SchwartzMap E ℂ :=
  (normalized_radial_cutoff_compact b n).toSchwartzMap (Complex.ofRealCLM.contDiff.comp
    ((mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id)).mul
      (hb.comp (contDiff_const.smul contDiff_id))))

theorem normalized_radian_cutoff_apply (b : E → ℝ) (hb : ContDiff ℝ ∞ b) (n : ℕ) (ξ : E) :
    fixedRadianProfile (normalizedRadianCutoffProfile b hb n) ξ =
      mikhlinBall (((n : ℝ)+1)⁻¹ • (tau⁻¹ • ξ)) * b ξ := by
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  change ((↑(mikhlinBall (((n : ℝ)+1)⁻¹ • (tau⁻¹ • ξ)) * b (tau • (tau⁻¹ • ξ))) : ℂ)).re = _
  rw [Complex.ofReal_re, smul_smul tau tau⁻¹ ξ, mul_inv_cancel₀ τp.ne', one_smul]

/-- The Fourier half-shift of a smooth order-one frequency profile is the
pointwise limit of its actual absolutely convergent Weyl midpoint kernels. -/
theorem separated_radian_weyl_is_midpoint_kernel_limit (b : E → ℝ) (hb : ContDiff ℝ ∞ b)
    (A : ℝ) (A0 : 0 ≤ A) (growth : ∀ ξ, ‖b ξ‖ ≤ A * (1 + ‖ξ‖))
    (f u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n => ∫ y, ((SchwartzMap.fourierTransformCLE ℂ).symm (normalizedRadianCutoffProfile b hb n)) (x - y) *
      f ((1 / 2 : ℝ) • (x + y)) * u y) atTop
      (𝓝 (separatedRadianQuantization (1 / 2) b f u x)) := by
  let a n := normalizedRadianCutoffProfile b hb n
  let bn n := fixedRadianProfile (a n)
  have realA (n : ℕ) (ξ : E) : ((a n ξ).re : ℂ) = a n ξ := by
    change ((↑(mikhlinBall (((n : ℝ)+1)⁻¹ • ξ) * b (tau • ξ)) : ℂ).re : ℂ) = _
    rw [Complex.ofReal_re]
    rfl
  have uniform (n : ℕ) (ξ : E) : ‖bn n ξ‖ ≤ A * (1 + ‖ξ‖) := by
    change ‖fixedRadianProfile (normalizedRadianCutoffProfile b hb n) ξ‖ ≤ _
    rw [normalized_radian_cutoff_apply, norm_mul, Real.norm_of_nonneg mikhlinBall.nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) mikhlinBall.le_one).trans (growth ξ)
  have near (ξ : E) : ∀ᶠ n : ℕ in atTop, bn n ξ = b ξ := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖tau⁻¹ • ξ‖
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : ‖tau⁻¹ • ξ‖ ≤ (n : ℝ)+1 := hN.trans ((Nat.cast_le.mpr hn).trans (le_add_of_nonneg_right zero_le_one))
    have inside : (((n : ℝ)+1)⁻¹ • (tau⁻¹ • ξ)) ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
      exact (div_le_iff₀ (by positivity)).mpr (by simpa only [one_mul] using h)
    change fixedRadianProfile (normalizedRadianCutoffProfile b hb n) ξ = b ξ
    rw [normalized_radian_cutoff_apply, mikhlinBall.one_of_mem_closedBall inside, one_mul]
  have lookup (ξ : E) : Tendsto (fun n => bn n ξ) atTop (𝓝 (b ξ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [near ξ] with n hn
    exact hn.symm
  have hLim := separated_radian_quantization_tendsto (1 / 2) bn b
    (fun n => fixed_radian_profile_measurable (a n)) hb.continuous.measurable A A0 uniform growth
    lookup f u x
  simpa only [bn, separated_radian_weyl_fixed_profile_kernel _ (realA _), a] using hLim

end Burnett.A03
