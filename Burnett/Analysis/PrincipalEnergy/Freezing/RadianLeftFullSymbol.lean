import Burnett.Analysis.PrincipalEnergy.Freezing.CompactOrderZeroModes
import Burnett.Analysis.PrincipalEnergy.Freezing.WeylPhysicalLimit
import Burnett.Analysis.TransportWard.Weyl.Amplitude.RadianLeftFullSymbol

set_option autoImplicit false
set_option maxHeartbeats 3000000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.RicciSymbol
open scoped ENNReal ContDiff FourierTransform

theorem radian_left_quantization_frozen (b : E → ℝ) (u : SchwartzMap E ℂ) (x : E) :
    radianLeftQuantization (fun _ ξ => (b ξ : ℂ)) u x = radianAction b u x := by
  simp only [radianLeftQuantization, radian_action_fourier_integral, mul_assoc]

/-- A separated expansion of the actual left symbol passes through its
real-frequency Fourier integral under the stated summable growth budget. -/
theorem radian_left_quantization_separated_sum {ι : Type} [Countable ι]
    (a : E → E → ℂ) (f : ι → SchwartzMap E ℂ) (b : ι → E → ℝ)
    (bM : ∀ i, Measurable (b i)) (D : ι → ℝ) (D0 : ∀ i, 0 ≤ D i) (hD : Summable D)
    (growth : ∀ i ξ, ‖b i ξ‖ ≤ D i * (1 + ‖ξ‖))
    (U : ℝ) (U0 : 0 ≤ U) (uniform : ∀ i x, ‖f i x‖ ≤ U)
    (reconstruction : ∀ x ξ, ξ ≠ 0 → HasSum (fun i => f i x * (b i ξ : ℂ)) (a x ξ))
    (u : SchwartzMap E ℂ) (x : E) :
    radianLeftQuantization a u x = ∑' i, separatedRadianQuantization 0 (b i) (f i) u x := by
  let F := SchwartzMap.fourierTransformCLM ℂ u
  let J (ξ : E) := (1 + tau * ‖ξ‖) * ‖F ξ‖
  let G (i : ι) (ξ : E) :=
    patchFourierPhase ξ x * (f i x * (b i (tau • ξ) : ℂ)) * F ξ
  have τp : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have JI : Integrable J volume := by
    have h := F.integrable.norm.add ((F.integrable_pow_mul volume 1).const_mul tau)
    apply h.congr
    filter_upwards with ξ
    change ‖F ξ‖ + tau * (‖ξ‖ ^ 1 * ‖F ξ‖) = J ξ
    rw [pow_one]
    dsimp only [J]
    ring
  have GB (i : ι) (ξ : E) : ‖G i ξ‖ ≤ (U * D i) * J ξ := by
    simp only [G, norm_mul, patch_fourier_phase_norm, one_mul, Complex.norm_real, J]
    have h := growth i (tau • ξ)
    rw [norm_smul, Real.norm_of_nonneg τp.le] at h
    calc
      _ ≤ (U * (D i * (1 + tau * ‖ξ‖))) * ‖F ξ‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul (uniform i x) h (norm_nonneg _) U0) (norm_nonneg _)
      _ = _ := by ring
  have GI (i : ι) : Integrable (G i) volume := by
    have pM : Measurable (fun ξ : E => patchFourierPhase ξ x) :=
      (patch_fourier_phase_continuous.comp (continuous_id.prodMk continuous_const)).measurable
    have bM' : Measurable (fun ξ : E => (b i (tau • ξ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp ((bM i).comp (continuous_const.smul continuous_id).measurable)
    exact (JI.const_mul (U * D i)).mono'
      ((pM.mul (measurable_const.mul bM')).mul F.continuous.measurable).aestronglyMeasurable
      (Eventually.of_forall (GB i))
  have Si : Summable (fun i => ∫ ξ, ‖G i ξ‖) := by
    apply Summable.of_nonneg_of_le (fun i => integral_nonneg (fun _ => norm_nonneg _)) _
      ((hD.mul_left U).mul_right (∫ ξ, J ξ))
    intro i
    exact (integral_mono (GI i).norm (JI.const_mul _) (GB i)).trans_eq (integral_const_mul _ _)
  have eq (i : ι) : (∫ ξ, G i ξ) = separatedRadianQuantization 0 (b i) (f i) u x := by
    rw [separated_radian_quantization_left _ (bM i)
      (slanted_radian_symbol_growth 0 _ (D i) (D0 i) (growth i)), radian_action_fourier_integral, ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun ξ => by
      change patchFourierPhase ξ x * (f i x * (b i (tau • ξ) : ℂ)) * F ξ =
        f i x * (patchFourierPhase ξ x * ((b i (tau • ξ) : ℂ) * F ξ))
      ring
  simp_rw [← eq]
  rw [integral_tsum_of_summable_integral_norm GI Si]
  apply integral_congr_ae
  have ae0 : ∀ᵐ ξ : E ∂volume, ξ ≠ 0 := by
    rw [ae_iff]
    simp
  filter_upwards [ae0] with ξ hξ
  have nt : tau • ξ ≠ 0 := smul_ne_zero τp.ne' hξ
  have s := ((reconstruction x (tau • ξ) nt).mul_left (patchFourierPhase ξ x)).mul_right (F ξ)
  exact s.tsum_eq.symm

end Burnett.A03
