import Burnett.Analysis.PrincipalEnergy.Freezing.AngularDifferential
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualSymbolInputs
import Burnett.Analysis.TransportWard.Weyl.PatchFourierPhase

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Burnett.RicciSymbol Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace

private theorem frequency_translate_temperate (q : E) :
    Function.HasTemperateGrowth (fun ξ : E => ξ - q) := by
  apply Function.HasTemperateGrowth.of_fderiv ?_ (differentiable_id.sub_const q)
    (k := 1) (C := 1 + ‖q‖)
  · intro ξ
    change ‖ξ - q‖ ≤ (1 + ‖q‖) * (1 + ‖ξ‖)^1
    apply (norm_sub_le _ _).trans
    rw [pow_one]
    nlinarith [mul_nonneg (norm_nonneg q) (norm_nonneg ξ)]
  · have eq : fderiv ℝ (fun ξ : E => ξ - q) = fun _ => ContinuousLinearMap.id ℝ E :=
      funext fun ξ => ((hasFDerivAt_id ξ).sub_const q).fderiv
    change Function.HasTemperateGrowth (fderiv ℝ (fun ξ : E => ξ - q))
    rw [eq]
    exact Function.HasTemperateGrowth.const _

private def translatedSpectrum (q : E) : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.compCLM ℂ (frequency_translate_temperate q) ⟨1, 1 + ‖q‖, fun ξ => by
    have tri := norm_add_le (ξ - q) q
    rw [sub_add_cancel] at tri
    rw [pow_one]
    exact tri.trans (by nlinarith [mul_nonneg (norm_nonneg q) (norm_nonneg (ξ - q))])⟩

theorem inverse_fourier_frequency_translate (F : E → ℂ) (q x : E) :
    𝓕⁻ (fun ξ => F (ξ - q)) x = patchFourierPhase q x * (𝓕⁻ F) x := by
  rw [Real.fourierIntegralInv_eq', Real.fourierIntegralInv_eq']
  let G := fun ζ : E => patchFourierPhase (ζ + q) x * F ζ
  calc
    _ = ∫ ξ, G (ξ - q) := by
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [G, sub_add_cancel, Burnett.Microlocal.Overlap.baseFourierPhase, smul_eq_mul]
    _ = ∫ ξ, G ξ := by
      simpa only [sub_eq_add_neg] using integral_add_right_eq_self G (-q)
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      simp only [G, patch_fourier_phase_add, smul_eq_mul]
      change patchFourierPhase ξ x * patchFourierPhase q x * F ξ =
        patchFourierPhase q x * (patchFourierPhase ξ x * F ξ)
      ring

/-- Actual Schwartz modulation, constructed by translation of its spectrum. -/
def patchModulatedSchwartz (q : E) (u : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm
    (translatedSpectrum q (SchwartzMap.fourierTransformCLE ℂ u))

theorem patch_modulated_schwartz_fourier (q : E) (u : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (patchModulatedSchwartz q u : E → ℂ) ξ = 𝓕 (u : E → ℂ) (ξ - q) := by
  change SchwartzMap.fourierTransformCLE ℂ (patchModulatedSchwartz q u) ξ = _
  unfold patchModulatedSchwartz
  rw [ContinuousLinearEquiv.apply_symm_apply]
  rfl

theorem patch_modulated_schwartz_apply (q : E) (u : SchwartzMap E ℂ) (x : E) :
    patchModulatedSchwartz q u x = patchFourierPhase q x * u x := by
  unfold patchModulatedSchwartz
  rw [SchwartzMap.fourierTransformCLE_symm_apply]
  change 𝓕⁻ (fun ξ => 𝓕 (u : E → ℂ) (ξ - q)) x = _
  rw [inverse_fourier_frequency_translate]
  rw [u.continuous.fourier_inversion u.integrable (SchwartzMap.fourierTransformCLM ℂ u).integrable]

/-- Fourier modulation conjugates a frequency shift in the literal radian action. -/
theorem radian_action_shift (m : E → ℝ) (q : E) (u : SchwartzMap E ℂ) (x : E) :
    radianAction (fun ξ => m (ξ + tau • q)) u x =
      patchFourierPhase (-q) x * radianAction m (patchModulatedSchwartz q u) x := by
  simp only [← radianActionSpectrum_inverse]
  rw [← inverse_fourier_frequency_translate]
  congr 2
  funext ξ
  simp only [radianActionSpectrum, patch_modulated_schwartz_fourier, sub_neg_eq_add, add_sub_cancel_right, smul_add]

/-- The angular translated multipliers all have the same L³ constant. -/
theorem exists_translated_angular_action_L3_bound :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (b : E → ℝ), ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0} →
      (∀ t : ℝ, 0 < t → ∀ ξ, b (t • ξ) = t * b ξ) →
      ∀ D : ℝ, 0 ≤ D →
      (∀ n : ℕ, n ≤ 7 → ∀ ξ ∈ sphere (0 : E) 1, ‖iteratedFDeriv ℝ n b ξ‖ ≤ D) →
      ∀ (v q : E) (u : SchwartzMap E ℂ),
        let w := radianAction (fun ξ => angularDifferential b v (ξ + tau • q)) u
        MemLp w (ENNReal.ofReal 3) volume ∧
          eLpNorm w (ENNReal.ofReal 3) volume ≤
            ENNReal.ofReal (K * ‖v‖ * D) * eLpNorm (u : E → ℂ) (ENNReal.ofReal 3) volume := by
  obtain ⟨K, hK, bound⟩ := homogeneous_multiplier_all_Lp_sphere_bound 3 (by norm_num)
  refine ⟨K, hK, ?_⟩
  intro b hb hom D hD jet v q u w
  let m := angularDifferential b v
  let z := patchModulatedSchwartz q u
  let p := ENNReal.ofReal 3
  have A0 : 0 ≤ ‖v‖ * D := mul_nonneg (norm_nonneg _) hD
  obtain ⟨_, S, _, normBound, _, hAction⟩ := bound m (angular_differential_contDiffOn b hb v)
    (fun t ht ξ => angular_differential_homogeneous b hb hom v t ht ξ) (‖v‖ * D) A0
    (fun n hn ξ hξ => angular_differential_sphere_jet b hb v jet n hn ξ hξ)
  have hz : MemLp (radianAction m z) p volume := (Lp.memLp (S (z.toLp p volume))).ae_eq (hAction z)
  have hphase (x : E) : ‖w x‖ = ‖radianAction m z x‖ := by
    change ‖radianAction (fun ξ => m (ξ + tau • q)) u x‖ = _
    rw [radian_action_shift, norm_mul, patch_fourier_phase_norm, one_mul]
  have wmeas : AEStronglyMeasurable w volume := by
    have hc : Continuous (fun x : E => (-q, x)) := continuous_const.prodMk continuous_id
    have hmeas := (patch_fourier_phase_continuous.comp hc).aestronglyMeasurable (μ := (volume : Measure E))
    have eq : w = fun x => patchFourierPhase (-q) x * radianAction m z x :=
      funext fun x => radian_action_shift m q u x
    rw [eq]
    exact hmeas.mul hz.1
  have outEq : eLpNorm (S (z.toLp p volume) : E → ℂ) p volume =
      eLpNorm (radianAction m z) p volume := eLpNorm_congr_ae (hAction z)
  have inEq : eLpNorm (z : E → ℂ) p volume = eLpNorm (u : E → ℂ) p volume := by
    apply eLpNorm_congr_norm_ae
    filter_upwards with x
    simp only [z, patch_modulated_schwartz_apply, norm_mul, patch_fourier_phase_norm, one_mul]
  have outFin := (Lp.memLp (S (z.toLp p volume))).eLpNorm_lt_top
  have inFin := (z.memLp p volume).eLpNorm_lt_top
  have boundReal := normBound (z.toLp p volume)
  rw [Lp.norm_def, SchwartzMap.norm_toLp] at boundReal
  have boundENN : eLpNorm (S (z.toLp p volume) : E → ℂ) p volume ≤
      ENNReal.ofReal (K * (‖v‖ * D)) * eLpNorm (z : E → ℂ) p volume := by
    apply (ENNReal.toReal_le_toReal outFin.ne
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top inFin).ne).mp
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (mul_nonneg hK A0)] using boundReal
  refine ⟨hz.congr_norm wmeas (Eventually.of_forall (fun x => (hphase x).symm)), ?_⟩
  rw [eLpNorm_congr_norm_ae (Eventually.of_forall hphase), ← outEq, mul_assoc, ← inEq]
  exact boundENN

end Burnett.A03
