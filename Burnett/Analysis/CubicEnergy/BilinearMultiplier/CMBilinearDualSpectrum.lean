import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDualFourier
import Burnett.Analysis.SignedFourierWindow.KernelDualPower
import Burnett.Analysis.Microlocal.AngularCommutator.FourierRepresentation

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow

open MeasureTheory Burnett.Fourier Burnett.Microlocal.AngularCommutator
open scoped FourierTransform RealInnerProductSpace

/-- The bilinear multiplier's actual spectrum in the sum frequency. -/
def jointBilinearSpectrum (m : Joint → ℝ) (f g : SchwartzMap E ℂ) (ζ : E) : ℂ :=
  ∫ ξ, (m (ζ - ξ, ξ) : ℂ) *
    (𝓕 (f : E → ℂ) (ζ - ξ) * 𝓕 (g : E → ℂ) ξ)

private def outputShear : Joint ≃ᵐ Joint :=
  (MeasurableEquiv.prodComm : Joint ≃ᵐ Joint).trans
    ((MeasurableEquiv.shearSubRight E).trans MeasurableEquiv.prodComm)

private theorem outputShear_measurePreserving :
    MeasurePreserving outputShear (volume : Measure Joint) volume := by
  rw [Measure.volume_eq_prod E E]
  exact measurePreserving_sub_prod (volume : Measure E) volume

private theorem amplitude_with_phase_integrable (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (f g : SchwartzMap E ℂ) (x : E) :
    Integrable (fun y => (m y : ℂ) * testCarrier f g x y) :=
  (testCarrier_integrable f g x).bdd_mul
    (Complex.continuous_ofReal.measurable.comp hm).aestronglyMeasurable
    ⟨D, fun y => by simpa only [Complex.norm_real] using hD y⟩

private theorem spectral_slice_bound (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (f g : SchwartzMap E ℂ) :
    ∃ B : ℝ, ∀ ζ, Integrable (fun ξ => (m (ζ - ξ, ξ) : ℂ) *
      (𝓕 (f : E → ℂ) (ζ - ξ) * 𝓕 (g : E → ℂ) ξ)) ∧
      ‖jointBilinearSpectrum m f g ζ‖ ≤ B := by
  let F := SchwartzMap.fourierTransformCLM ℂ f
  let G := SchwartzMap.fourierTransformCLM ℂ g
  obtain ⟨A, hA⟩ : ∃ A : ℝ, ∀ ξ : E, ‖F ξ‖ ≤ A := ⟨_, fun ξ => F.norm_le_seminorm ℂ ξ⟩
  have hD₀ : 0 ≤ D := (norm_nonneg (m 0)).trans (hD 0)
  refine ⟨∫ ξ, D * A * ‖G ξ‖, fun ζ => ?_⟩
  let W := fun ξ : E => (m (ζ - ξ, ξ) : ℂ) * (F (ζ - ξ) * G ξ)
  have mh : Measurable (fun ξ : E => ζ - ξ) := measurable_const.sub measurable_id
  have mw : Measurable W :=
    (Complex.continuous_ofReal.measurable.comp (hm.comp (mh.prodMk measurable_id))).mul
      ((F.continuous.measurable.comp mh).mul G.continuous.measurable)
  have pointwise (ξ : E) : ‖W ξ‖ ≤ D * A * ‖G ξ‖ := by
    change ‖(m (ζ - ξ, ξ) : ℂ) * (F (ζ - ξ) * G ξ)‖ ≤ D * A * ‖G ξ‖
    rw [norm_mul, norm_mul, Complex.norm_real, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hD _) (hA _) (norm_nonneg _) hD₀) (norm_nonneg _)
  have dom : Integrable (fun ξ : E => D * A * ‖G ξ‖) := G.integrable.norm.const_mul (D * A)
  have hW : Integrable W := dom.mono' mw.aestronglyMeasurable (Filter.Eventually.of_forall pointwise)
  exact ⟨hW, (norm_integral_le_integral_norm W).trans (integral_mono hW.norm dom pointwise)⟩

/-- Both endpoints of the joint shear are absolutely integrable. The summed
frequency spectrum is integrable and square-integrable. -/
theorem jointBilinearSpectrum_integrable_memLp (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (f g : SchwartzMap E ℂ) :
    Integrable (jointBilinearSpectrum m f g) ∧ MemLp (jointBilinearSpectrum m f g) 2 volume := by
  have h := outputShear_measurePreserving.integrable_comp_of_integrable
    (amplitude_with_phase_integrable m hm hD f g 0)
  rw [Measure.volume_eq_prod E E] at h
  have hi : Integrable (jointBilinearSpectrum m f g) := by
    apply h.integral_prod_left.congr
    filter_upwards with ζ
    apply integral_congr_ae
    filter_upwards with ξ
    change (m (ζ - ξ, ξ) : ℂ) * testCarrier f g 0 (ζ - ξ, ξ) =
      (m (ζ - ξ, ξ) : ℂ) * (𝓕 (f : E → ℂ) (ζ - ξ) * 𝓕 (g : E → ℂ) ξ)
    simp [testCarrier]
  obtain ⟨B, hB⟩ := spectral_slice_bound m hm hD f g
  have hp := bounded_L1_norm_power hi B (fun ζ => (hB ζ).2) 2 (by norm_num)
  refine ⟨hi, (memLp_two_iff_integrable_sq_norm hi.1).mpr ?_⟩
  simpa only [Real.rpow_two] using hp

/-- The physical joint multiplier is exactly the inverse Fourier integral
of its sum-frequency spectrum. -/
theorem jointBilinear_eq_inverse_spectrum (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (f g : SchwartzMap E ℂ) :
    jointBilinear m f g = 𝓕⁻ (jointBilinearSpectrum m f g) := by
  funext x
  let A := fun y : Joint => (m y : ℂ) * testCarrier f g x y
  have h := outputShear_measurePreserving.integrable_comp_of_integrable
    (amplitude_with_phase_integrable m hm hD f g x)
  rw [Measure.volume_eq_prod E E] at h
  calc
    jointBilinear m f g x = ∫ y : Joint, A y := rfl
    _ = ∫ y : Joint, (A ∘ outputShear) y := (outputShear_measurePreserving.integral_comp' A).symm
    _ = ∫ ζ : E, ∫ ξ : E, (A ∘ outputShear) (ζ, ξ) := by
      simpa only [Measure.volume_eq_prod E E] using integral_prod (A ∘ outputShear) h
    _ = 𝓕⁻ (jointBilinearSpectrum m f g) x := by
      rw [Real.fourierIntegralInv_eq']
      apply integral_congr_ae
      filter_upwards with ζ
      rw [smul_eq_mul, jointBilinearSpectrum, ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with ξ
      change (m (ζ - ξ, ξ) : ℂ) * testCarrier f g x (ζ - ξ, ξ) = _
      simp only [testCarrier, ← inner_add_left, sub_add_cancel]
      ring

/-- The genuine project L² Fourier isometry sends the pointwise output to
the stated physical spectrum almost everywhere. -/
theorem jointBilinear_fourierL2 (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (f g : SchwartzMap E ℂ) :
    ∃ hu : MemLp (jointBilinear m f g) 2 volume,
      (fourierL2Equiv (hu.toLp (jointBilinear m f g)) : E → ℂ) =ᵐ[volume]
        jointBilinearSpectrum m f g := by
  obtain ⟨hi, hg⟩ := jointBilinearSpectrum_integrable_memLp m hm hD f g
  let v := hg.toLp (jointBilinearSpectrum m f g)
  let T := fourierL2Equiv (V := E)
  have he : (T.symm v : E → ℂ) =ᵐ[volume] jointBilinear m f g := by
    rw [jointBilinear_eq_inverse_spectrum m hm hD f g]
    exact fourierL2Equiv_symm_eq_inverse_ae_of_integrable _ hi hg
  have hu := (Lp.memLp (T.symm v)).ae_eq he
  have eq : hu.toLp (jointBilinear m f g) = T.symm v :=
    Lp.ext (hu.coeFn_toLp.trans he.symm)
  refine ⟨hu, ?_⟩
  rw [eq]
  change (T (T.symm v) : E → ℂ) =ᵐ[volume] _
  rw [T.apply_symm_apply]
  exact hg.coeFn_toLp

private theorem jointBilinearSpectrum_mul_output (m : Joint → ℝ) (c : E → ℝ)
    (f g : SchwartzMap E ℂ) (ζ : E) :
    jointBilinearSpectrum (fun y => c (y.1 + y.2) * m y) f g ζ =
      (c ζ : ℂ) * jointBilinearSpectrum m f g ζ := by
  unfold jointBilinearSpectrum
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with ξ
  rw [sub_add_cancel, Complex.ofReal_mul, mul_assoc]

/-- A bounded real linear output multiplier acts by its exact value at the
sum frequency. The physical interpretation uses the project L² multiplier. -/
theorem jointBilinear_fourierMultiplier_output (m : Joint → ℝ) (hm : Measurable m)
    {D : ℝ} (hD : ∀ y, ‖m y‖ ≤ D) (c : E → ℝ) (hc : Measurable c)
    (M : BoundedSymbol E) (hM : ∀ ζ, M ζ = (c ζ : ℂ)) (f g : SchwartzMap E ℂ) :
    ∃ hu : MemLp (jointBilinear m f g) 2 volume,
      (fourierMultiplier M (hu.toLp (jointBilinear m f g)) : E → ℂ) =ᵐ[volume]
        jointBilinear (fun y => c (y.1 + y.2) * m y) f g := by
  obtain ⟨hu, hf⟩ := jointBilinear_fourierL2 m hm hD f g
  refine ⟨hu, ?_⟩
  let v := symbolL2 M (fourierL2Equiv (hu.toLp (jointBilinear m f g)))
  let W := fun ζ => M ζ * jointBilinearSpectrum m f g ζ
  have hv : (v : E → ℂ) =ᵐ[volume] W := by
    refine (symbolL2_ae M _).trans ?_
    filter_upwards [hf] with ζ h
    simp only [W, h]
  have hW := (Lp.memLp v).ae_eq hv
  have eq : v = hW.toLp W := Lp.ext (hv.trans hW.coeFn_toLp.symm)
  have hi : Integrable W := (jointBilinearSpectrum_integrable_memLp m hm hD f g).1.bdd_mul
    M.measurable ⟨M.bound, M.norm_le⟩
  change (fourierL2Equiv.symm v : E → ℂ) =ᵐ[volume] _
  rw [eq]
  refine (fourierL2Equiv_symm_eq_inverse_ae_of_integrable W hi hW).trans (.of_forall ?_)
  intro x
  let a := fun y : Joint => c (y.1 + y.2) * m y
  have ha : Measurable a := (hc.comp (measurable_fst.add measurable_snd)).mul hm
  have hA (y : Joint) : ‖a y‖ ≤ M.bound * D := by
    change ‖c (y.1 + y.2) * m y‖ ≤ M.bound * D
    rw [norm_mul, ← Complex.norm_real, ← hM (y.1 + y.2)]
    exact mul_le_mul (M.norm_le _) (hD y) (norm_nonneg _) M.bound_nonneg
  have heq : jointBilinearSpectrum a f g = W := funext fun ζ => by
    rw [jointBilinearSpectrum_mul_output, ← hM]
  change 𝓕⁻ W x = jointBilinear a f g x
  rw [jointBilinear_eq_inverse_spectrum a ha hA f g, heq]

end Burnett.A02.FrequencySplit
