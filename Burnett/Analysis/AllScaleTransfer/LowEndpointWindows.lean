import Burnett.Analysis.AllScaleTransfer.RadialThirdCutoff
import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest

set_option autoImplicit false
set_option maxHeartbeats 2100000

noncomputable section

namespace Burnett.A05
open Burnett.Analysis.ShiftedFourierWindow

open MeasureTheory Set Metric Finset
open Burnett.A02.FrequencySplit
open Burnett.Analysis.CapFourier
open scoped ContDiff FourierTransform BigOperators

def endpointLowProfile : SchwartzMap E ℂ :=
  CMBilinearDual.schwartzBump radialBallBump

private theorem high_profile_exists :
    ∃ a : SchwartzMap E ℂ, (∀ x, a x = (mikhlinWindow x : ℂ)) ∧
      HasCompactSupport (a : E → ℂ) ∧ (∀ x, a x ≠ 0 → 1/2 < ‖x‖ ∧ ‖x‖ < 2) := by
  simpa only [mul_one] using
    mikhlin_profile_exists (fun _ => (1 : ℝ)) contDiffOn_const

def endpointHighProfile : SchwartzMap E ℂ := Classical.choose high_profile_exists

theorem endpointHighProfile_properties :
    (∀ x, endpointHighProfile x = (mikhlinWindow x : ℂ)) ∧
      HasCompactSupport (endpointHighProfile : E → ℂ) ∧
      (∀ x, endpointHighProfile x ≠ 0 → 1/2 < ‖x‖ ∧ ‖x‖ < 2) :=
  Classical.choose_spec high_profile_exists

private theorem thick_profile_compact : HasCompactSupport (fun x : E => (thickProductCutoff 1 x : ℂ)) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0:E) 4)
  intro x hx
  have hnz : thickProductCutoff 1 x ≠ 0 := by
    intro h
    exact hx (by simp only [h, Complex.ofReal_zero])
  have hb := tsupport_thickProductCutoff_subset (by norm_num : (0 : ℝ) < 1)
    (subset_tsupport _ hnz)
  exact (mem_closedBall.2 (by simpa only [dist_zero_right, mul_one] using hb.2))

/-- The actual product-frequency cutoff at unit radius, as a Schwartz profile. -/
def endpointThickProfile : SchwartzMap E ℂ :=
  thick_profile_compact.toSchwartzMap (Complex.ofRealCLM.contDiff.comp (thickProductCutoff_smooth 1))

theorem endpointThickProfile_apply (x : E) : endpointThickProfile x = (thickProductCutoff 1 x : ℂ) := rfl

private theorem mikhlinBall_eq_radialBallBump : mikhlinBall = radialBallBump := rfl

private theorem tau_cancel_scale (s : ℝ) : tau*s⁻¹*tau⁻¹ = s⁻¹ := by
  have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos).ne'
  rw [mul_comm tau s⁻¹, mul_assoc, mul_inv_cancel₀ hτ, mul_one]

/-- The three Schwartz profiles in their actual manuscript radian scales. -/
theorem endpoint_profiles_at_radian_frequency (r : ℝ) (gap : ℕ) (ξ : E) :
    let p := tau⁻¹ • ξ
    endpointLowProfile ((tau*(r/(2 : ℝ)^gap)⁻¹) • p) =
        (radialLowCutoff (r/(2 : ℝ)^gap) ξ : ℂ) ∧
      endpointHighProfile ((tau*r⁻¹) • p) = (radialAnnularCutoff r ξ : ℂ) ∧
      endpointThickProfile ((tau*r⁻¹) • p) = (thickProductCutoff r ξ : ℂ) := by
  dsimp only
  simp only [smul_smul, tau_cancel_scale]
  refine ⟨rfl, ?_, ?_⟩
  · rw [endpointHighProfile_properties.1, mikhlinWindow, mikhlinBall_eq_radialBallBump]
    change (↑(radialBallBump (r⁻¹ • ξ) - radialBallBump ((2 : ℝ) • (r⁻¹ • ξ))) : ℂ) =
      ↑(radialBallBump (r⁻¹ • ξ) - radialBallBump ((r/2)⁻¹ • ξ))
    rw [smul_smul, inv_div, div_eq_mul_inv]
  · rw [endpointThickProfile_apply, thickProductCutoff, thickProductCutoff]
    simp only [inv_one, radialLowCutoff, smul_smul]
    rw [inv_div]
    norm_num [div_eq_mul_inv]

/-- Six fixed rescalings between the endpoints 1/4 and 16 of the partition. -/
def endpointPartScale (k : ℕ) : ℝ := (2 : ℝ)^k * (1/4)

theorem endpointPartScale_pos (k : ℕ) : 0 < endpointPartScale k := by
  unfold endpointPartScale
  positivity

private theorem endpoint_part_compact (k : ℕ) :
    HasCompactSupport (fun x : E =>
      endpointHighProfile x * endpointThickProfile ((endpointPartScale k)⁻¹ • x)) :=
  endpointHighProfile_properties.2.1.mul_right

/-- The product of the fixed thick window and a narrow dyadic window,
expressed in the narrow window's own frequency coordinates. -/
def endpointThickPart (k : ℕ) : SchwartzMap E ℂ :=
  (endpoint_part_compact k).toSchwartzMap
    ((endpointHighProfile.smooth _).mul
      ((endpointThickProfile.smooth _).comp (contDiff_const.smul contDiff_id)))

theorem endpointThickPart_properties (k : ℕ) :
    HasCompactSupport (endpointThickPart k : E → ℂ) ∧
      (∀ x, endpointThickPart k x ≠ 0 → 1/2 < ‖x‖ ∧ ‖x‖ < 2) := by
  refine ⟨endpoint_part_compact k, ?_⟩
  intro x hx
  apply endpointHighProfile_properties.2.2 x
  intro hz
  apply hx
  change endpointHighProfile x * endpointThickProfile ((endpointPartScale k)⁻¹ • x) = 0
  rw [hz, zero_mul]

/-- The fixed thick profile is exactly the sum of six rescaled narrow profiles. -/
theorem endpointThickProfile_six_parts (x : E) :
    (∑ k : Fin 6, endpointThickPart k (endpointPartScale k • x)) = endpointThickProfile x := by
  classical
  have part (k : Fin 6) : endpointThickPart k (endpointPartScale k • x) =
      endpointHighProfile (endpointPartScale k • x) * endpointThickProfile x := by
    change endpointHighProfile (endpointPartScale k • x) *
      endpointThickProfile ((endpointPartScale k)⁻¹ • (endpointPartScale k • x)) = _
    rw [smul_smul, inv_mul_cancel₀ (endpointPartScale_pos k).ne', one_smul]
  simp_rw [part, ← Finset.sum_mul]
  by_cases hz : endpointThickProfile x = 0
  · simp only [hz, mul_zero]
  have hnonzero : thickProductCutoff 1 x ≠ 0 := by
    intro h
    exact hz (by rw [endpointThickProfile_apply, h, Complex.ofReal_zero])
  have hS := tsupport_thickProductCutoff_subset (by norm_num : (0 : ℝ) < 1)
    (subset_tsupport _ hnonzero)
  have hlo : mikhlinBall ((1/4 : ℝ) • x) = 1 := by
    apply mikhlinBall.one_of_mem_closedBall
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1/4)]
    change (1/4)*‖x‖ ≤ 1
    linarith [hS.2]
  have hhi : mikhlinBall ((16 : ℝ) • x) = 0 := by
    apply mikhlinBall.zero_of_le_dist
    rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 16)]
    change 2 ≤ 16*‖x‖
    linarith [hS.1]
  have ha (y : E) : endpointHighProfile y = ((mikhlinWindow y * (1:ℝ) : ℝ) : ℂ) := by
    simpa only [mul_one] using endpointHighProfile_properties.1 y
  have ht := mikhlin_telescope (fun _ => (1:ℝ)) (fun _ _ _ => rfl) endpointHighProfile ha
    (1/4) (by norm_num) x 6
  have hsum : (∑ k : Fin 6, endpointHighProfile (endpointPartScale k • x)) = 1 := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => endpointHighProfile (endpointPartScale n • x))]
    simpa only [endpointPartScale, show (2:ℝ)^6*(1/4) = 16 by norm_num, hlo, hhi,
      sub_zero, Complex.ofReal_one, mul_one] using ht
  rw [hsum, one_mul]

private theorem schwartz_6_sum_apply (f : Fin 6 → SchwartzMap E ℂ) (ξ : E) :
    (∑ k, f k) ξ = ∑ k, f k ξ := by
  change SchwartzMap.coeHom E ℂ (∑ k, f k) ξ = _
  rw [map_sum, Finset.sum_apply]
  rfl

private theorem endpointThick_windowTest_six_parts (f : SchwartzMap E ℂ) (t : ℝ) :
    windowTest endpointThickProfile f t =
      ∑ k : Fin 6, windowTest (endpointThickPart k) f (endpointPartScale k * t) := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ξ : 1
  rw [map_sum, schwartz_6_sum_apply]
  change 𝓕 (windowTest endpointThickProfile f t : E → ℂ) ξ =
    ∑ k : Fin 6, 𝓕 (windowTest (endpointThickPart k) f (endpointPartScale k*t) : E → ℂ) ξ
  simp_rw [windowTest_fourier, ← smul_smul, ← Finset.mul_sum, endpointThickProfile_six_parts]

/-- The exact decomposition for the actual zero-modulation spatial window. -/
theorem shiftedEndpointThickWindow_six_parts (f : SchwartzMap E ℂ) {t : ℝ} (ht : 0 < t) (x : E) :
    shiftedWindowOperator endpointThickProfile f t 0 x =
      ∑ k : Fin 6, shiftedWindowOperator (endpointThickPart k) f (endpointPartScale k*t) 0 x := by
  have h (a : SchwartzMap E ℂ) {s : ℝ} (hs : 0 < s) :
      shiftedWindowOperator a f s 0 x = windowTest a f s x := by
    simpa only [neg_zero, zero_div, smul_zero, sub_zero] using (windowTest_translate a f s 0 hs x (0:E)).symm
  rw [h _ ht, endpointThick_windowTest_six_parts, schwartz_6_sum_apply]
  exact Finset.sum_congr rfl (fun k _ => (h _ (mul_pos (endpointPartScale_pos k) ht)).symm)

end Burnett.A05
