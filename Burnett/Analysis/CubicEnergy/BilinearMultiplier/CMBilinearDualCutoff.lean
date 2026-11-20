import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualDensity
import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit.CMBilinearDual
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Metric Set Filter
open scoped ContDiff ENNReal FourierTransform RealInnerProductSpace Topology

def inputCutoffRadius (n : ℕ) : ℝ := (n : ℝ) + 1

private theorem radius_one_le (n : ℕ) : 1 ≤ inputCutoffRadius n := by
  unfold inputCutoffRadius
  exact le_add_of_nonneg_left (Nat.cast_nonneg n)

theorem inputCutoffRadius_pos (n : ℕ) : 0 < inputCutoffRadius n :=
  zero_lt_one.trans_le (radius_one_le n)

/-- Simultaneous removal of frequencies near zero and near infinity. -/
def inputAnnularMask (n : ℕ) (ξ : E) : ℝ :=
  mikhlinBall ((inputCutoffRadius n)⁻¹ • ξ) - mikhlinBall (inputCutoffRadius n • ξ)

theorem inputAnnularMask_contDiff (n : ℕ) : ContDiff ℝ ∞ (inputAnnularMask n) :=
  (mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id)).sub
    (mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id))

theorem inputAnnularMask_norm_le (n : ℕ) (ξ : E) : ‖inputAnnularMask n ξ‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_le]
  unfold inputAnnularMask
  constructor <;> linarith [mikhlinBall.nonneg (x := (inputCutoffRadius n)⁻¹ • ξ),
    mikhlinBall.le_one (x := (inputCutoffRadius n)⁻¹ • ξ),
    mikhlinBall.nonneg (x := inputCutoffRadius n • ξ),
    mikhlinBall.le_one (x := inputCutoffRadius n • ξ)]

private theorem bump_one {ξ : E} (h : ‖ξ‖ ≤ 1) : mikhlinBall ξ = 1 :=
  mikhlinBall.one_of_mem_closedBall (by simpa only [mem_closedBall, dist_zero_right] using h)

private theorem bump_zero {ξ : E} (h : 2 ≤ ‖ξ‖) : mikhlinBall ξ = 0 :=
  mikhlinBall.zero_of_le_dist (by simpa only [dist_zero_right] using h)

private theorem compare_scales (n : ℕ) (ξ : E) :
    ‖(inputCutoffRadius n)⁻¹ • ξ‖ ≤ ‖inputCutoffRadius n • ξ‖ := by
  rw [norm_smul, norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (inputCutoffRadius_pos n).le),
    Real.norm_of_nonneg (inputCutoffRadius_pos n).le]
  exact mul_le_mul_of_nonneg_right
    ((inv_le_one_of_one_le₀ (radius_one_le n)).trans (radius_one_le n)) (norm_nonneg _)

private theorem mask_zero_near (n : ℕ) {ξ : E} (h : ‖ξ‖ ≤ (inputCutoffRadius n)⁻¹) :
    inputAnnularMask n ξ = 0 := by
  have R := inputCutoffRadius_pos n
  have hc : ‖inputCutoffRadius n • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg R.le]
    exact (mul_le_mul_of_nonneg_left h R.le).trans_eq (mul_inv_cancel₀ R.ne')
  rw [inputAnnularMask, bump_one ((compare_scales n ξ).trans hc), bump_one hc, sub_self]

private theorem mask_zero_far (n : ℕ) {ξ : E} (h : 2 * inputCutoffRadius n ≤ ‖ξ‖) :
    inputAnnularMask n ξ = 0 := by
  have R := inputCutoffRadius_pos n
  have hc : 2 ≤ ‖(inputCutoffRadius n)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr R.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ R).mpr h
  rw [inputAnnularMask, bump_zero hc, bump_zero (hc.trans (compare_scales n ξ)), sub_self]

theorem inputAnnularMask_eventually_one {ξ : E} (hn : ξ ≠ 0) :
    ∀ᶠ n : ℕ in atTop, inputAnnularMask n ξ = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_ge (max ‖ξ‖ (2 / ‖ξ‖))
  filter_upwards [eventually_ge_atTop N] with n hnN
  have hnr : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnN
  have hR : max ‖ξ‖ (2 / ‖ξ‖) ≤ inputCutoffRadius n := by
    unfold inputCutoffRadius
    linarith
  have lo : ‖(inputCutoffRadius n)⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (inputCutoffRadius_pos n).le), ← div_eq_inv_mul]
    exact (div_le_one (inputCutoffRadius_pos n)).mpr ((le_max_left _ _).trans hR)
  have hi : 2 ≤ ‖inputCutoffRadius n • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inputCutoffRadius_pos n).le]
    exact (div_le_iff₀ (norm_pos_iff.mpr hn)).mp ((le_max_right _ _).trans hR)
  rw [inputAnnularMask, bump_one lo, bump_zero hi, sub_zero]

private def maskedSpectrum (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (n : ℕ) :
    SchwartzMap E ℂ := by
  let A := fun ξ => (inputAnnularMask n ξ : ℂ) * F ξ
  have hc : HasCompactSupport A := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2 * inputCutoffRadius n))
    intro ξ hξ
    by_contra h
    have hx : 2 * inputCutoffRadius n < ‖ξ‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using h
    exact hξ (by simp [A, mask_zero_far n hx.le])
  have smooth : ContDiff ℝ ∞ A := by
    apply contDiff_iff_contDiffAt.mpr
    intro ξ
    by_cases hξ : ξ = 0
    · subst ξ
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) 0).congr_of_eventuallyEq
      filter_upwards [ball_mem_nhds (0 : E) (inv_pos.mpr (inputCutoffRadius_pos n))] with v hv
      have hv' : ‖v‖ < (inputCutoffRadius n)⁻¹ := by simpa only [mem_ball, dist_zero_right] using hv
      simp [A, mask_zero_near n hv'.le]
    · have hcut := (Complex.ofRealCLM.contDiff.comp (inputAnnularMask_contDiff n)).contDiffAt (x := ξ)
      exact hcut.mul (hF.contDiffAt (isOpen_compl_singleton.mem_nhds hξ))
  exact hc.toSchwartzMap smooth

/-- The smooth compact annular spectrum, pulled back to a Schwartz input. -/
def annularInput (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (n : ℕ) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (maskedSpectrum F hF n)

theorem annularInput_fourier (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (n : ℕ) (ξ : E) :
    𝓕 (annularInput F hF n : E → ℂ) ξ = (inputAnnularMask n ξ : ℂ) * F ξ :=
  congrArg (fun f : SchwartzMap E ℂ => f ξ)
    ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply (maskedSpectrum F hF n))

theorem annularInput_eq_inverse (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0}) (n : ℕ) :
    (annularInput F hF n : E → ℂ) = 𝓕⁻ (fun ξ => (inputAnnularMask n ξ : ℂ) * F ξ) :=
  SchwartzMap.fourierTransformCLE_symm_apply _ _

private theorem annular_mask_ae :
    ∀ᵐ ξ ∂(volume : Measure E), ∀ᶠ n : ℕ in atTop, inputAnnularMask n ξ = 1 := by
  filter_upwards [(Set.countable_singleton (0 : E)).ae_notMem volume] with ξ hξ
  exact inputAnnularMask_eventually_one hξ

/-- The approximating spectra converge in frequency L¹ to the exact spectrum. -/
theorem annularInput_fourier_L1 (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0})
    (hi : Integrable F) :
    Tendsto (fun n => eLpNorm ((𝓕 (annularInput F hF n : E → ℂ)) - F) 1 volume) atTop (𝓝 0) := by
  have lim : ∀ᵐ ξ ∂(volume : Measure E), Tendsto
      (fun n => (inputAnnularMask n ξ : ℂ) * F ξ) atTop (𝓝 (F ξ)) :=
    annular_mask_ae.mono fun ξ h => tendsto_const_nhds.congr' (h.mono fun n hn => by
      simp only [hn, Complex.ofReal_one, one_mul])
  have hmeas (n : ℕ) : AEStronglyMeasurable (fun ξ => (inputAnnularMask n ξ : ℂ) * F ξ) volume :=
    (Complex.continuous_ofReal.comp (inputAnnularMask_contDiff n).continuous).aestronglyMeasurable.mul hi.1
  have hb (n : ℕ) (ξ : E) : ‖(inputAnnularMask n ξ : ℂ) * F ξ‖ ≤ ‖F ξ‖ := by
    rw [norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _) (inputAnnularMask_norm_le n ξ)
  simpa only [annularInput_fourier, eLpNorm_one_eq_lintegral_enorm, Pi.sub_apply, ← ofReal_norm_eq_enorm]
    using tendsto_lintegral_norm_of_dominated_convergence hmeas hi.norm.2
      (fun n => Eventually.of_forall (hb n)) lim

/-- Removal of the two frequency cutoffs recovers the actual inverse integral
at every physical point when the uncut spectrum is integrable. -/
theorem annularInput_tendsto_pointwise (F : E → ℂ) (hF : ContDiffOn ℝ ∞ F {ξ | ξ ≠ 0})
    (hi : Integrable F) (x : E) :
    Tendsto (fun n => annularInput F hF n x) atTop (𝓝 (𝓕⁻ F x)) := by
  let w := fun ξ : E => Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
  have hw : Continuous w := by dsimp only [w]; fun_prop
  have wn (ξ : E) : ‖w ξ‖ = 1 := by simp [w, Complex.norm_exp]
  simp_rw [show ∀ n, annularInput F hF n x =
    𝓕⁻ (fun ξ => (inputAnnularMask n ξ : ℂ) * F ξ) x from
    fun n => congrFun (annularInput_eq_inverse F hF n) x, Real.fourierIntegralInv_eq', smul_eq_mul]
  refine tendsto_integral_of_dominated_convergence (fun ξ => ‖F ξ‖) (fun n => ?_) hi.norm
    (fun n => Eventually.of_forall fun ξ => ?_) (annular_mask_ae.mono fun ξ h => ?_)
  · exact hw.aestronglyMeasurable.mul
      ((Complex.continuous_ofReal.comp (inputAnnularMask_contDiff n).continuous).aestronglyMeasurable.mul hi.1)
  · change ‖w ξ * ((inputAnnularMask n ξ : ℂ) * F ξ)‖ ≤ ‖F ξ‖
    rw [norm_mul, wn, one_mul, norm_mul, Complex.norm_real]
    exact mul_le_of_le_one_left (norm_nonneg _) (inputAnnularMask_norm_le n ξ)
  · apply tendsto_const_nhds.congr'
    filter_upwards [h] with n hn
    rw [hn, Complex.ofReal_one, one_mul]

end Burnett.A02.FrequencySplit.CMBilinearDual
