import Burnett.Analysis.PrincipalEnergy.Freezing.ModeFourierMoment
import Burnett.Analysis.PrincipalEnergy.Freezing.LocalizedSpatialProfilesSchwartz

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.A03

open MeasureTheory Metric Set Burnett.Geometry.ConnectionDifference Burnett.RicciSymbol
open Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform RealInnerProductSpace

/-- The fixed spatial Fourier cutoff in the complex test space. -/
def patchCutoffSchwartz (P : ℝ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : E) P) : SchwartzMap E ℂ :=
  let compact : HasCompactSupport ρ :=
    (isCompact_closedBall (0 : E) P).of_isClosed_subset isClosed_closure
      (hSupport.trans ball_subset_closedBall)
  (compact.comp_left (g := Complex.ofReal) Complex.ofReal_zero).toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hρ)

private theorem patch_fourier_moment_combination_le (r : ℕ) (u v : SchwartzMap E ℂ)
    (α β : ℂ) (hα : ‖α‖ ≤ 1) (hβ : ‖β‖ ≤ 1) :
    patchFourierMoment r (α • u + β • v) ≤ patchFourierMoment r u + patchFourierMoment r v := by
  let L := SchwartzMap.fourierTransformCLM (V := E) (E := ℂ) ℂ
  let U := L u
  let V := L v
  let S := L (α • u + β • v)
  have iU := U.integrable_pow_mul volume r
  have iV := V.integrable_pow_mul volume r
  change (∫ η, ‖η‖ ^ r * ‖S η‖) ≤
    (∫ η, ‖η‖ ^ r * ‖U η‖) + ∫ η, ‖η‖ ^ r * ‖V η‖
  rw [← integral_add iU iV]
  apply integral_mono (S.integrable_pow_mul volume r) (iU.add iV)
  intro η
  have eq : S η = α * U η + β * V η := by
    dsimp only [S, U, V]
    rw [map_add, map_smul, map_smul]
    rfl
  change ‖η‖ ^ r * ‖S η‖ ≤ ‖η‖ ^ r * ‖U η‖ + ‖η‖ ^ r * ‖V η‖
  rw [eq, ← mul_add]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply (norm_add_le _ _).trans
  rw [norm_mul, norm_mul]
  exact add_le_add (mul_le_of_le_one_left (norm_nonneg _) hα) (mul_le_of_le_one_left (norm_nonneg _) hβ)

private theorem patch_spatial_phase (P : ℝ) (k : Index → ℤ) (y : E) :
    patchFourierPhase (spatialModeFrequency P k) y =
      Complex.exp ((spatialModePhase P k y : ℂ) * Complex.I) := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, spatialModePhase, real_inner_comm y]

private theorem patch_negative_spatial_phase (P : ℝ) (k : Index → ℤ) (y : E) :
    patchFourierPhase (-spatialModeFrequency P k) y =
      Complex.exp (-(spatialModePhase P k y : ℂ) * Complex.I) := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, spatialModePhase, inner_neg_left, mul_neg, Complex.ofReal_neg,
    real_inner_comm (spatialModeFrequency P k) y]

private theorem patch_unscaled_moment_bound
    (P : ℝ) (k : Index → ℤ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : E) P) (j : Fin 2) (r : ℕ) :
    let f := localizedRealSpatialModeSchwartz P k ρ hρ hSupport 0 1 zero_lt_one j
    let a := patchCutoffSchwartz P ρ hρ hSupport
    patchFourierMoment r f ≤ 2 * ((1 + ‖spatialModeFrequency P k‖) ^ r * 2 ^ r *
      (patchFourierMoment 0 a + patchFourierMoment r a)) := by
  intro f a
  let q := spatialModeFrequency P k
  let u := patchModulatedSchwartz q a
  let v := patchModulatedSchwartz (-q) a
  have plus := patch_fourier_moment_modulated r a q
  have minus := patch_fourier_moment_modulated r a (-q)
  rw [norm_neg] at minus
  have modes : patchFourierMoment r u + patchFourierMoment r v ≤ 2 *
      ((1 + ‖q‖) ^ r * 2 ^ r * (patchFourierMoment 0 a + patchFourierMoment r a)) := by
    simpa only [two_mul] using add_le_add plus minus
  have hTwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  have half : ‖(1 / 2 : ℂ)‖ ≤ 1 := by rw [norm_div, norm_one, hTwo]; norm_num
  have halfI : ‖(Complex.I / 2 : ℂ)‖ ≤ 1 := by rw [norm_div, Complex.norm_I, hTwo]; norm_num
  have values (y : E) :
      u y = Complex.exp ((spatialModePhase P k y : ℂ) * Complex.I) * (ρ y : ℂ) ∧
      v y = Complex.exp (-(spatialModePhase P k y : ℂ) * Complex.I) * (ρ y : ℂ) := by
    dsimp only [u, v, q]
    rw [patch_modulated_schwartz_apply, patch_modulated_schwartz_apply, patch_spatial_phase,
      patch_negative_spatial_phase]
    exact ⟨rfl, rfl⟩
  by_cases hj : j = 0
  · have eq : f = (1 / 2 : ℂ) • u + (1 / 2 : ℂ) • v := by
      ext y
      rw [localized_real_spatial_mode_schwartz_apply, localizedRealSpatialModeProfile, if_pos hj]
      simp only [localizedSpatialCosineProfile, inv_one, sub_zero, one_smul, Complex.ofReal_mul,
        Complex.ofReal_cos, Complex.cos, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul,
        (values y).1, (values y).2]
      ring
    rw [eq]
    exact (patch_fourier_moment_combination_le r u v _ _ half half).trans modes
  · have negHalfI : ‖-(Complex.I / 2 : ℂ)‖ ≤ 1 := by simpa only [norm_neg] using halfI
    have eq : f = (-(Complex.I / 2) : ℂ) • u + (Complex.I / 2 : ℂ) • v := by
      ext y
      rw [localized_real_spatial_mode_schwartz_apply, localizedRealSpatialModeProfile, if_neg hj]
      simp only [localizedSpatialSineProfile, inv_one, sub_zero, one_smul, Complex.ofReal_mul,
        Complex.ofReal_sin, Complex.sin, SchwartzMap.add_apply, SchwartzMap.smul_apply, smul_eq_mul,
        (values y).1, (values y).2]
      ring
    rw [eq]
    exact (patch_fourier_moment_combination_le r u v _ _ negHalfI halfI).trans modes

/-- Actual cosine and sine modes have Fourier moments with the stated
length and lattice frequency dependence, uniformly in the center. -/
theorem localized_real_spatial_mode_fourier_moment
    (P : ℝ) (k : Index → ℤ) (ρ : E → ℝ) (hρ : ContDiff ℝ ∞ ρ)
    (hSupport : tsupport ρ ⊆ ball (0 : E) P) (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (j : Fin 2) (r : ℕ) :
    let f := localizedRealSpatialModeSchwartz P k ρ hρ hSupport c ℓ hℓ j
    let a := patchCutoffSchwartz P ρ hρ hSupport
    patchFourierMoment r f ≤ (ℓ ^ r)⁻¹ * (2 * ((1 + ‖spatialModeFrequency P k‖) ^ r * 2 ^ r *
      (patchFourierMoment 0 a + patchFourierMoment r a))) := by
  intro f a
  let u := localizedRealSpatialModeSchwartz P k ρ hρ hSupport 0 1 zero_lt_one j
  have eq : (f : E → ℂ) = fun x => u (ℓ⁻¹ • (x - c)) := by
    funext x
    dsimp only [f, u]
    rw [localized_real_spatial_mode_schwartz_apply, localized_real_spatial_mode_schwartz_apply]
    unfold localizedRealSpatialModeProfile localizedSpatialCosineProfile localizedSpatialSineProfile
    by_cases hj : j = 0
    · simp only [if_pos hj, inv_one, sub_zero, one_smul]
    · simp only [if_neg hj, inv_one, sub_zero, one_smul]
  rw [eq, patch_fourier_moment_affine r _ c ℓ hℓ]
  apply mul_le_mul_of_nonneg_left (patch_unscaled_moment_bound P k ρ hρ hSupport j r)
  positivity

end Burnett.A03
