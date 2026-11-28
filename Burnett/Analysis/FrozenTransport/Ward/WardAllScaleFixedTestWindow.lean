import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicHighPassTest
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
set_option maxRecDepth 5800
set_option maxHeartbeats 2800000

noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A02.FrequencySplit
open scoped ContDiff

private theorem wardTestTau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def wardFixedTestBump : ContDiffBump (0 : E) :=
  ⟨tau⁻¹ / 2, tau⁻¹, half_pos (inv_pos.mpr wardTestTau_pos), half_lt_self (inv_pos.mpr wardTestTau_pos)⟩

/-- Its physical radius is one in the original radian normalization. -/
def wardFixedTestCutoff : SchwartzMap E ℂ :=
  (wardFixedTestBump.hasCompactSupport.comp_left Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp wardFixedTestBump.contDiff)

theorem wardFixedTestCutoff_real (ξ : E) : ((wardFixedTestCutoff ξ).re : ℂ) = wardFixedTestCutoff ξ := by
  change ((Complex.ofReal (wardFixedTestBump ξ)).re : ℂ) = Complex.ofReal (wardFixedTestBump ξ)
  rw [Complex.ofReal_re]

theorem wardFixedTestCutoff_profile_zero (ξ : E) (hξ : 1 < ‖ξ‖) :
    fixedRadianProfile wardFixedTestCutoff ξ = 0 := by
  change (Complex.ofReal (wardFixedTestBump (tau⁻¹ • ξ))).re = 0
  rw [Complex.ofReal_re]
  apply wardFixedTestBump.zero_of_le_dist
  change tau⁻¹ ≤ dist (tau⁻¹ • ξ) 0
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr wardTestTau_pos.le)]
  exact le_mul_of_one_le_right (inv_nonneg.mpr wardTestTau_pos.le) hξ.le

theorem wardFixedTestCutoff_profile_one (ξ : E) (hξ : ‖ξ‖ ≤ 1/2) :
    fixedRadianProfile wardFixedTestCutoff ξ = 1 := by
  change (Complex.ofReal (wardFixedTestBump (tau⁻¹ • ξ))).re = 1
  rw [Complex.ofReal_re]
  apply wardFixedTestBump.one_of_mem_closedBall
  change dist (tau⁻¹ • ξ) 0 ≤ tau⁻¹ / 2
  rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr wardTestTau_pos.le)]
  exact (mul_le_mul_of_nonneg_left hξ (inv_nonneg.mpr wardTestTau_pos.le)).trans_eq (mul_one_div _ _)

theorem wardFixedTestCutoff_odd (a : E → ℝ) (ha : ∀ ξ, a (-ξ) = -a ξ) (ξ : E) :
    fixedInfraredSymbol wardFixedTestCutoff 0 a (-ξ) = -fixedInfraredSymbol wardFixedTestCutoff 0 a ξ := by
  have h : fixedRadianProfile wardFixedTestCutoff (-ξ) = fixedRadianProfile wardFixedTestCutoff ξ := by
    change (Complex.ofReal (wardFixedTestBump (tau⁻¹ • (-ξ)))).re =
      (Complex.ofReal (wardFixedTestBump (tau⁻¹ • ξ))).re
    rw [smul_neg, wardFixedTestBump.neg]
  rw [fixedInfraredSymbol, fixedInfraredSymbol, h, ha ξ]
  simp [fixedRadianProfile]

end Burnett.C02
