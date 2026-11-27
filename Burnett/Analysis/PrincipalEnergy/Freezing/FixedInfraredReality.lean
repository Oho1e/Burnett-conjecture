import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure
import Burnett.Analysis.PrincipalEnergy.Freezing.RealSkewTest
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open Metric
open scoped ComplexConjugate ContDiff

private def freezingInfraredBump : ContDiffBump (0 : E) :=
  ⟨1 / 2, 1, by norm_num, by norm_num⟩

private theorem freezingTauPos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

/-- A fixed real radial infrared cutoff in the normalized frequency variable. -/
def radialFreezingInfraredCutoff : SchwartzMap E ℂ :=
  ((freezingInfraredBump.hasCompactSupport.comp_smul freezingTauPos.ne').comp_left
    Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp
      (freezingInfraredBump.contDiff.comp (contDiff_const.smul contDiff_id)))

private theorem radialFreezingInfraredCutoff_apply (ξ : E) :
    radialFreezingInfraredCutoff ξ = (freezingInfraredBump (tau • ξ) : ℂ) := rfl

private theorem radialFreezingInfrared_profile (ξ : E) :
    fixedRadianProfile radialFreezingInfraredCutoff ξ = freezingInfraredBump ξ := by
  simp only [fixedRadianProfile, radialFreezingInfraredCutoff_apply, Complex.ofReal_re, smul_smul,
    mul_inv_cancel₀ freezingTauPos.ne', one_smul]

/-- The fixed infrared profile has the even symmetry and the two radial
plateaus used by the compact Weyl test. -/
theorem radialFreezingInfraredCutoff_spec :
    (∀ ξ, ((radialFreezingInfraredCutoff ξ).re : ℂ) = radialFreezingInfraredCutoff ξ) ∧
    (∀ ξ, fixedRadianProfile radialFreezingInfraredCutoff (-ξ) =
      fixedRadianProfile radialFreezingInfraredCutoff ξ) ∧
    (∀ ξ : E, ‖ξ‖ ≤ 1 / 2 → fixedRadianProfile radialFreezingInfraredCutoff ξ = 1) ∧
    (∀ ξ : E, 1 < ‖ξ‖ → fixedRadianProfile radialFreezingInfraredCutoff ξ = 0) := by
  refine ⟨fun ξ => ?_, fun ξ => ?_, fun ξ h => ?_, fun ξ h => ?_⟩
  · rw [radialFreezingInfraredCutoff_apply, Complex.ofReal_re]
  · simpa only [radialFreezingInfrared_profile] using freezingInfraredBump.neg ξ
  · rw [radialFreezingInfrared_profile]
    exact freezingInfraredBump.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using h)
  · rw [radialFreezingInfrared_profile]
    exact freezingInfraredBump.zero_of_le_dist (by simpa only [dist_zero_right] using h.le)

/-- An even infrared cutoff preserves the oddness that makes the actual
scalar skew test real on real fields. -/
theorem radianSkewAction_fixedInfrared_preserves_real (cut : SchwartzMap E ℂ)
    (hEven : ∀ ξ, fixedRadianProfile cut (-ξ) = fixedRadianProfile cut ξ)
    (b : E → ℝ) (hOdd : ∀ ξ, b (-ξ) = -b ξ)
    (u : SchwartzMap E ℂ) (hReal : ∀ x, conj (u x) = u x) (x : E) :
    conj ((-Complex.I) * radianAction (fixedInfraredSymbol cut 0 b) u x) =
      (-Complex.I) * radianAction (fixedInfraredSymbol cut 0 b) u x := by
  have odd : ∀ ξ, fixedInfraredSymbol cut 0 b (-ξ) = -fixedInfraredSymbol cut 0 b ξ := by
    intro ξ
    have hz (η : E) : fixedRadianProfile (0 : SchwartzMap E ℂ) η = 0 := by
      simp [fixedRadianProfile]
    simp only [fixedInfraredSymbol, hEven ξ, hOdd ξ, hz, add_zero, mul_neg]
  exact radianSkewAction_preserves_real (fixedInfraredSymbol cut 0 b) odd u hReal x

end Burnett.A02.FrequencySplit
