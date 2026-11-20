import Burnett.Analysis.CubicEnergy.JointMultiplier.JointDyadicPlacements

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Finset
open scoped ENNReal ContDiff

def kernelMoment (A : Joint → ℂ) (j k : ℕ) : ℝ≥0∞ :=
  ∫⁻ y : Joint, ENNReal.ofReal ((1+‖y.1‖)^j*((1+‖y.2‖)^k)*‖blockKernel A y‖)

theorem kernelMoment_lt_top (A : Joint → ℂ) (ha : HasCompactSupport A) (hs : ContDiff ℝ ∞ A)
    (j k : ℕ) : kernelMoment A j k < ⊤ := by
  have hi := blockKernel_mixed_moment A ha hs j k
  unfold kernelMoment
  exact hi.hasFiniteIntegral.trans_eq' (by
    apply lintegral_congr
    intro y
    exact (Real.enorm_eq_ofReal (by positivity)).symm)

def ratioCost (c : ℝ) (k : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal ((max 1 ‖c⁻¹‖)^k)

private theorem shiftWeight_le (c : ℝ) (j : ℕ) (y : E) :
    shiftWeight c j y ≤ ratioCost c j * ENNReal.ofReal ((1+‖y‖)^j) := by
  let D := max 1 ‖c⁻¹‖
  have d0 : 0≤D := zero_le_one.trans (le_max_left _ _)
  have le : 1+‖(-c⁻¹) • y‖ ≤ D*(1+‖y‖) := by
    rw [norm_smul,norm_neg,mul_add,mul_one]
    exact add_le_add (le_max_left _ _) (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  unfold shiftWeight ratioCost
  rw [← ENNReal.ofReal_mul (pow_nonneg d0 _),← mul_pow]
  exact ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (by positivity) le _)

/-- A bound for the spatial products at each fixed kernel translation
integrates with the weighted norm of that same reference Fourier kernel. -/
theorem tested_window_sum_bound (A : Joint → ℂ) (ha : HasCompactSupport A) (hs : ContDiff ℝ ∞ A)
    (f g h a b c : SchwartzMap E ℂ) (u v w t : ℝ) (n j k : ℕ) (C G : ℝ≥0∞)
    (bound : ∀ y : Joint, sumWindowEnorm f g h a b c u v w t n y ≤
      C*shiftWeight u j y.1*shiftWeight v k y.2*G) :
    ‖∑ i : Fin n, windowBlock A (dyadicScale t i) f g h a b c u v w‖ₑ ≤
      C*ratioCost u j*ratioCost v k*kernelMoment A j k*G := by
  let K := blockKernel A
  let W := fun y : Joint => ENNReal.ofReal ((1+‖y.1‖)^j*((1+‖y.2‖)^k)*‖K y‖)
  let D := C*ratioCost u j*ratioCost v k*G
  let N := fun y : Joint => sumWindowEnorm f g h a b c u v w t n y
  have hbound := testedBlocks_enorm_le A ha hs n (fun i => dyadicScale t i)
    (fun i => windowTest a f (u*dyadicScale t i)) (fun i => windowTest b g (v*dyadicScale t i))
    (fun i => windowTest c h (w*dyadicScale t i))
  have H : ∀ y : Joint, ‖K y‖ₑ*N y ≤ W y*D := by
    intro y
    have E : W y = ENNReal.ofReal ((1+‖y.1‖)^j)*ENNReal.ofReal ((1+‖y.2‖)^k)*‖K y‖ₑ := by
      unfold W
      rw [ENNReal.ofReal_mul (by positivity),ENNReal.ofReal_mul (by positivity),ofReal_norm_eq_enorm]
    calc
      _ ≤ ‖K y‖ₑ*(C*(ratioCost u j*ENNReal.ofReal ((1+‖y.1‖)^j))*
          (ratioCost v k*ENNReal.ofReal ((1+‖y.2‖)^k))*G) :=
        mul_le_mul_left' ((bound y).trans (mul_le_mul_right' (mul_le_mul' (mul_le_mul_left'
          (shiftWeight_le u j y.1) C) (shiftWeight_le v k y.2)) G)) _
      _ = _ := by rw [E]; unfold D; ac_rfl
  change ‖∑ i : Fin n, windowBlock A (dyadicScale t i) f g h a b c u v w‖ₑ ≤
    C*ratioCost u j*ratioCost v k*(∫⁻ y,W y)*G
  have contK : Continuous K := (blockKernel_integrable A ha hs).2
  have mW : Measurable W := by unfold W; fun_prop
  calc
    _ ≤ ∫⁻ y : Joint, ‖K y‖ₑ*N y := hbound
    _ ≤ ∫⁻ y : Joint, W y*D := lintegral_mono H
    _ = (∫⁻ y,W y)*D := lintegral_mul_const D mW
    _ = _ := by unfold D; ac_rfl

end Burnett.A02.FrequencySplit
