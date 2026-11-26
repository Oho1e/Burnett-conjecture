import Burnett.Analysis.CubicEnergy.HighSlotCommutator.RadianHighDerivativeCommutator
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Burnett.Analysis.Fourier.SchwartzParseval

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A08

open MeasureTheory Filter Metric
open Burnett.A02.FrequencySplit
open Burnett.Fourier (schwartz_parseval)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped ENNReal FourierTransform RealInnerProductSpace Topology ContDiff

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private def radialBallBump : ContDiffBump (0 : E) := ⟨1, 2, by norm_num, by norm_num⟩

private def radialLowCutoff (r : ℝ) (x : E) : ℝ := radialBallBump (r⁻¹ • x)

private theorem radialLowCutoff_eq_one {r : ℝ} (hr : 0 < r) {x : E} (hx : ‖x‖ ≤ r) :
    radialLowCutoff r x = 1 := by
  apply radialBallBump.one_of_mem_closedBall
  rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
    ← div_eq_inv_mul]
  exact (div_le_one hr).2 hx

/-- The actual Schwartz upper cutoff in the original radian frequency. -/
def upperFrequencyCutoff (Λ : ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  windowTest (CMBilinearDual.schwartzBump radialBallBump) f (tau * Λ⁻¹)

theorem upperFrequencyCutoff_profile :
    ContDiff ℝ ∞ (radialBallBump : E → ℝ) ∧ HasCompactSupport (radialBallBump : E → ℝ) ∧
      (∀ x : E, radialBallBump (-x) = radialBallBump x) ∧
      (∀ x : E, ‖x‖ ≤ 1 → radialBallBump x = 1) := by
  refine ⟨radialBallBump.contDiff, radialBallBump.hasCompactSupport, radialBallBump.neg, ?_⟩
  intro x hx
  apply radialBallBump.one_of_mem_closedBall
  simpa only [mem_closedBall, dist_zero_right] using hx

theorem upperFrequencyCutoff_fourier (Λ : ℝ) (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (upperFrequencyCutoff Λ f : E → ℂ) ξ =
      𝓕 (f : E → ℂ) ξ * (radialLowCutoff Λ (tau • ξ) : ℂ) := by
  rw [upperFrequencyCutoff, windowTest_fourier]
  change _ * (radialBallBump ((tau * Λ⁻¹) • ξ) : ℂ) =
    _ * (radialBallBump (Λ⁻¹ • (tau • ξ)) : ℂ)
  rw [smul_smul, mul_comm Λ⁻¹ tau]

private theorem radianFourier_as_cycles (f : SchwartzMap E ℂ) (ξ : E) :
    radianFourier f ξ = 𝓕 (f : E → ℂ) (tau⁻¹ • ξ) := by
  have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  simpa only [smul_smul, mul_inv_cancel₀ hτ, one_smul] using radianFourier_scaled f (tau⁻¹ • ξ)

/-- In radian frequency the symbol is literally the fixed real-even bump
evaluated at the physical frequency divided by Λ. -/
theorem upperFrequencyCutoff_radianFourier (Λ : ℝ) (f : SchwartzMap E ℂ) (ξ : E) :
    radianFourier (upperFrequencyCutoff Λ f) ξ =
      radianFourier f ξ * (radialLowCutoff Λ ξ : ℂ) := by
  have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  rw [radianFourier_as_cycles, upperFrequencyCutoff_fourier, radianFourier_as_cycles,
    smul_smul, mul_inv_cancel₀ hτ, one_smul]

def upperFrequencyError (Λ : ℝ) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  upperFrequencyCutoff Λ f - f

private theorem upperFrequencyError_fourier (Λ : ℝ) (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (upperFrequencyError Λ f : E → ℂ) ξ =
      𝓕 (f : E → ℂ) ξ * ((radialLowCutoff Λ (tau • ξ) : ℂ) - 1) := by
  change (SchwartzMap.fourierTransformCLM ℂ (upperFrequencyCutoff Λ f - f)) ξ = _
  rw [map_sub, SchwartzMap.sub_apply]
  change 𝓕 (upperFrequencyCutoff Λ f : E → ℂ) ξ - 𝓕 (f : E → ℂ) ξ = _
  rw [upperFrequencyCutoff_fourier]
  ring

private theorem norm_upperFrequencyError_fourier_le (Λ : ℝ) (f : SchwartzMap E ℂ) (ξ : E) :
    ‖𝓕 (upperFrequencyError Λ f : E → ℂ) ξ‖ ≤ ‖𝓕 (f : E → ℂ) ξ‖ := by
  have lo : 0 ≤ radialLowCutoff Λ (tau • ξ) := radialBallBump.nonneg
  have hi : radialLowCutoff Λ (tau • ξ) ≤ 1 := radialBallBump.le_one
  have hdiff : ‖(radialLowCutoff Λ (tau • ξ) : ℂ) - 1‖ ≤ 1 := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith only [lo], by linarith only [hi]⟩
  rw [upperFrequencyError_fourier, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) hdiff

private theorem schwartz_moment_integrable (f : SchwartzMap E ℂ) (k : ℕ) (hk : 0 < k) :
    Integrable (fun x : E => ‖f x‖ ^ k) := by
  have nonzero : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  simpa only [ENNReal.toReal_natCast, Real.rpow_natCast] using
    (f.memLp (k : ℝ≥0∞) volume).integrable_norm_rpow nonzero (ENNReal.natCast_ne_top k)

private def cutoffFourierMoment (k : ℕ) (Λ : ℝ) (f : SchwartzMap E ℂ) : ℝ :=
  ∫ ξ, ‖𝓕 (upperFrequencyError Λ f : E → ℂ) ξ‖ ^ k

private theorem cutoffFourierMoment_tendsto (f : SchwartzMap E ℂ) (k : ℕ) (hk : 0 < k) :
    Tendsto (fun Λ : ℝ => cutoffFourierMoment k Λ f) atTop (𝓝 0) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (F := fun (Λ : ℝ) (ξ : E) => ‖𝓕 (upperFrequencyError Λ f : E → ℂ) ξ‖ ^ k)
    (f := fun _ : E => (0 : ℝ)) (l := atTop)
    (fun ξ => ‖𝓕 (f : E → ℂ) ξ‖ ^ k)
    (Eventually.of_forall fun Λ =>
      ((SchwartzMap.fourierTransformCLM ℂ (upperFrequencyError Λ f)).continuous.norm.pow k).aestronglyMeasurable)
    (Eventually.of_forall fun Λ => Eventually.of_forall fun ξ => by
      rw [Real.norm_of_nonneg (pow_nonneg (norm_nonneg _) _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (norm_upperFrequencyError_fourier_le Λ f ξ) _)
    (schwartz_moment_integrable (SchwartzMap.fourierTransformCLM ℂ f) k hk)
    (Eventually.of_forall fun ξ => by
      apply Tendsto.congr' _ tendsto_const_nhds
      filter_upwards [eventually_ge_atTop (max (1 : ℝ) ‖tau • ξ‖)] with Λ hΛ
      have hp : 0 < Λ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hΛ)
      have h1 := radialLowCutoff_eq_one hp ((le_max_right _ _).trans hΛ)
      simp [upperFrequencyError_fourier, h1, hk.ne'])
  simpa only [cutoffFourierMoment, integral_zero] using h

private theorem norm_upperFrequencyError_le (Λ : ℝ) (f : SchwartzMap E ℂ) (x : E) :
    ‖upperFrequencyError Λ f x‖ ≤ cutoffFourierMoment 1 Λ f := by
  let g := upperFrequencyError Λ f
  have hi := congrFun (g.continuous.fourier_inversion g.integrable
    (SchwartzMap.fourierTransformCLM ℂ g).integrable) x
  change ‖g x‖ ≤ _
  rw [← hi, Real.fourierIntegralInv_eq_fourierIntegral_neg]
  simpa only [cutoffFourierMoment, pow_one] using
    (VectorFourier.norm_fourierIntegral_le_integral_norm Real.fourierChar volume (innerₗ E)
      (𝓕 (g : E → ℂ)) (-x))

private theorem lp_norm_of_moment (g : SchwartzMap E ℂ) (k : ℕ) (hk : 0 < k) :
    ‖g.toLp (k : ℝ≥0∞) volume‖ =
      (∫ x : E, ‖g x‖ ^ k) ^ ((k : ℝ)⁻¹) := by
  have nonzero : (k : ℝ≥0∞) ≠ 0 := by exact_mod_cast hk.ne'
  rw [SchwartzMap.norm_toLp,
    (g.memLp _ volume).eLpNorm_eq_integral_rpow_norm nonzero (ENNReal.natCast_ne_top k)]
  simp only [ENNReal.toReal_natCast, Real.rpow_natCast]
  exact ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg fun _ => by positivity) _)

theorem norm_upperFrequencyCutoff_L2_le (Λ : ℝ) (f : SchwartzMap E ℂ) :
    ‖(upperFrequencyCutoff Λ f).toLp 2 volume‖ ≤ ‖f.toLp 2 volume‖ := by
  let g := upperFrequencyCutoff Λ f
  have point (ξ : E) : ‖𝓕 (g : E → ℂ) ξ‖ ≤ ‖𝓕 (f : E → ℂ) ξ‖ := by
    have h : 0 ≤ radialLowCutoff Λ (tau • ξ) := radialBallBump.nonneg
    rw [upperFrequencyCutoff_fourier, norm_mul, Complex.norm_real, Real.norm_of_nonneg h]
    exact mul_le_of_le_one_right (norm_nonneg _) radialBallBump.le_one
  have imom : (∫ ξ, ‖𝓕 (g : E → ℂ) ξ‖ ^ 2) ≤ ∫ ξ, ‖𝓕 (f : E → ℂ) ξ‖ ^ 2 :=
    integral_mono (schwartz_moment_integrable (SchwartzMap.fourierTransformCLM ℂ g) 2 (by norm_num))
      (schwartz_moment_integrable (SchwartzMap.fourierTransformCLM ℂ f) 2 (by norm_num))
      (fun ξ => pow_le_pow_left₀ (norm_nonneg _) (point ξ) _)
  change ‖g.toLp ((2 : ℕ) : ℝ≥0∞) volume‖ ≤ ‖f.toLp ((2 : ℕ) : ℝ≥0∞) volume‖
  rw [lp_norm_of_moment g 2 (by norm_num), lp_norm_of_moment f 2 (by norm_num),
    ← schwartz_parseval g, ← schwartz_parseval f]
  exact Real.rpow_le_rpow (integral_nonneg fun _ => by positivity) imom (by positivity)

private theorem lp_norm_tendsto_of_moment (k : ℕ) (hk : 0 < k) (g : ℝ → SchwartzMap E ℂ)
    (lim : Tendsto (fun Λ : ℝ => ∫ x : E, ‖g Λ x‖ ^ k) atTop (𝓝 0)) :
    Tendsto (fun Λ : ℝ => ‖(g Λ).toLp (k : ℝ≥0∞) volume‖) atTop (𝓝 0) := by
  have hp : 0 < (k : ℝ)⁻¹ := inv_pos.mpr (by exact_mod_cast hk)
  simp_rw [lp_norm_of_moment _ k hk]
  simpa only [Function.comp_def, Real.zero_rpow hp.ne'] using
    (Real.continuous_rpow_const hp.le).continuousAt.tendsto.comp lim

/-- At fixed Schwartz input the actual upper cutoff tends strongly to identity
in L² and L⁴. Both estimates use the same cutoff and the same error. -/
theorem upperFrequencyError_tendsto_L2_L4 (f : SchwartzMap E ℂ) :
    Tendsto (fun Λ : ℝ => ‖(upperFrequencyError Λ f).toLp 2 volume‖) atTop (𝓝 0) ∧
      Tendsto (fun Λ : ℝ => ‖(upperFrequencyError Λ f).toLp 4 volume‖) atTop (𝓝 0) := by
  have moment₂ : Tendsto (fun Λ : ℝ => ∫ x : E, ‖upperFrequencyError Λ f x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [cutoffFourierMoment, schwartz_parseval] using cutoffFourierMoment_tendsto f 2 (by norm_num)
  have bound (Λ : ℝ) : (∫ x : E, ‖upperFrequencyError Λ f x‖ ^ 4) ≤
      (cutoffFourierMoment 1 Λ f) ^ 2 * ∫ x : E, ‖upperFrequencyError Λ f x‖ ^ 2 := by
    let g := upperFrequencyError Λ f
    let A := cutoffFourierMoment 1 Λ f
    have hp (x : E) : ‖g x‖ ^ 4 ≤ A ^ 2 * ‖g x‖ ^ 2 := by
      have hsq := pow_le_pow_left₀ (norm_nonneg _) (norm_upperFrequencyError_le Λ f x) 2
      calc
        _ = ‖g x‖ ^ 2 * ‖g x‖ ^ 2 := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    rw [← integral_const_mul]
    exact integral_mono (schwartz_moment_integrable g 4 (by norm_num))
      ((schwartz_moment_integrable g 2 (by norm_num)).const_mul _) hp
  have upper : Tendsto (fun Λ : ℝ =>
      (cutoffFourierMoment 1 Λ f) ^ 2 * ∫ x : E, ‖upperFrequencyError Λ f x‖ ^ 2) atTop (𝓝 0) := by
    simpa only [mul_zero] using ((cutoffFourierMoment_tendsto f 1 (by norm_num)).pow 2).mul moment₂
  have moment₄ := squeeze_zero (fun Λ => integral_nonneg (fun x => pow_nonneg (norm_nonneg _) _)) bound upper
  exact ⟨lp_norm_tendsto_of_moment 2 (by norm_num) _ moment₂,
    lp_norm_tendsto_of_moment 4 (by norm_num) _ moment₄⟩

theorem coordinateDerivative_upperFrequencyCutoff (j : Fin 4) (Λ : ℝ) (f : SchwartzMap E ℂ) :
    coordinateDerivative j (upperFrequencyCutoff Λ f) = upperFrequencyCutoff Λ (coordinateDerivative j f) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ξ
  change 𝓕 (coordinateDerivative j (upperFrequencyCutoff Λ f) : E → ℂ) ξ =
    𝓕 (upperFrequencyCutoff Λ (coordinateDerivative j f) : E → ℂ) ξ
  rw [← radianFourier_scaled, ← radianFourier_scaled, radianFourier_coordinateDerivative,
    upperFrequencyCutoff_radianFourier, upperFrequencyCutoff_radianFourier, radianFourier_coordinateDerivative]
  ring

/-- The derivative in the high-frequency remainder is the original
coordinate derivative, with convergence in the two norms used by the pairing. -/
theorem coordinateDerivative_upperFrequencyError_tendsto_L2_L4 (j : Fin 4) (f : SchwartzMap E ℂ) :
    Tendsto (fun Λ : ℝ => ‖(coordinateDerivative j (upperFrequencyError Λ f)).toLp 2 volume‖) atTop (𝓝 0) ∧
      Tendsto (fun Λ : ℝ => ‖(coordinateDerivative j (upperFrequencyError Λ f)).toLp 4 volume‖) atTop (𝓝 0) := by
  have eq (Λ : ℝ) : coordinateDerivative j (upperFrequencyError Λ f) = upperFrequencyError Λ (coordinateDerivative j f) := by
    unfold upperFrequencyError
    rw [show coordinateDerivative j (upperFrequencyCutoff Λ f - f) =
       coordinateDerivative j (upperFrequencyCutoff Λ f) - coordinateDerivative j f from
      (SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1)).map_sub _ _, coordinateDerivative_upperFrequencyCutoff]
  simpa only [eq] using upperFrequencyError_tendsto_L2_L4 (coordinateDerivative j f)

end Burnett.A08
