import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open Burnett.A02.FrequencySplit (E)
open ContinuousLinearMap MeasureTheory Metric
open scoped ContDiff Convolution NNReal

/-- A smooth coefficient at a prescribed uniform distance, with the original
global Lipschitz bound. The convolution only uses local integrability. -/
theorem exists_smooth_lipschitz_approximation (f : E → ℂ) (L : ℝ≥0)
    (hL : LipschitzWith L f) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : E → ℂ, ContDiff ℝ ∞ g ∧ LipschitzWith L g ∧
      ∀ x, ‖g x - f x‖ ≤ (L : ℝ) * ε := by
  let bump : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
  let k := bump.normed (volume : Measure E)
  let g := k ⋆[lsmul ℝ ℝ, volume] f
  have hf : Continuous f := hL.continuous
  refine ⟨g, bump.hasCompactSupport_normed.contDiff_convolution_left _ bump.contDiff_normed
    hf.locallyIntegrable, lipschitzWith_iff_norm_sub_le.2 ?_, ?_⟩
  · intro x y
    have hi (z : E) : Integrable (fun t : E => k t • f (z - t)) := by
      exact bump.hasCompactSupport_normed.convolutionExists_left_of_continuous_right
        (lsmul ℝ ℝ) bump.continuous_normed.locallyIntegrable hf z
    change ‖(∫ t, k t • f (x - t)) - ∫ t, k t • f (y - t)‖ ≤ _
    rw [← integral_sub (hi x) (hi y)]
    calc
      _ ≤ ∫ t : E, ‖k t • f (x - t) - k t • f (y - t)‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t : E, k t * ((L : ℝ) * ‖x - y‖) := by
        apply integral_mono ((hi x).sub (hi y)).norm (bump.integrable_normed.mul_const _)
        intro t
        change ‖k t • f (x - t) - k t • f (y - t)‖ ≤ k t * _
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (bump.nonneg_normed t)]
        apply mul_le_mul_of_nonneg_left _ (bump.nonneg_normed t)
        simpa only [sub_sub_sub_cancel_right] using hL.norm_sub_le (x - t) (y - t)
      _ = _ := by rw [integral_mul_const, bump.integral_normed, one_mul]
  · intro x
    rw [← dist_eq_norm]
    refine bump.dist_normed_convolution_le hf.aestronglyMeasurable (fun y hy => ?_)
    exact (hL.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le L.coe_nonneg)

end Burnett.P01
