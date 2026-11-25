import Burnett.Analysis.AngularCaps.LinearFourierChange

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.CapFourier

open MeasureTheory Filter
open Burnett.A02.FrequencySplit (Joint radianWeight radianFourier radianFourier_scaled jointVolume_haar tau)
open scoped ENNReal BigOperators

/-- Common change on the two independent frequencies in the original form. -/
def pairedFrequencyEquiv (A : Space ≃L[ℝ] Space) : Joint ≃L[ℝ] Joint := A.prodCongr A

@[simp] theorem pairedFrequencyEquiv_apply (A : Space ≃L[ℝ] Space) (p : Joint) :
    pairedFrequencyEquiv A p = (A p.1,A p.2) := rfl

theorem map_pairedFrequency_volume (A : Space ≃L[ℝ] Space) :
    Measure.map (pairedFrequencyEquiv A) (volume : Measure Joint) =
      ENNReal.ofReal ((linearJacobian A)⁻¹ ^ (2:ℕ)) • volume := by
  letI := jointVolume_haar
  let L := pairedFrequencyEquiv A
  have hdet : |LinearMap.det L.toLinearEquiv.toLinearMap| = (linearJacobian A)^2 := by
    change |LinearMap.det (A.toLinearEquiv.toLinearMap.prodMap A.toLinearEquiv.toLinearMap)| =
      |LinearMap.det A.toLinearEquiv.toLinearMap|^2
    rw [LinearMap.det_prodMap,abs_mul,pow_two]
  have h := Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure Joint)
    (f := L.toLinearEquiv.toLinearMap) (LinearEquiv.isUnit_det' L.toLinearEquiv).ne_zero
  rw [abs_inv,hdet,← inv_pow] at h
  exact h

theorem integral_comp_pairedFrequency (A : Space ≃L[ℝ] Space) (g : Joint → ℂ) :
    (∫ p, g (pairedFrequencyEquiv A p)) =
      (linearJacobian A)⁻¹ ^ (2:ℕ) • ∫ p, g p := by
  let e := (pairedFrequencyEquiv A).toHomeomorph.toMeasurableEquiv
  have h := e.measurableEmbedding.integral_map (μ := (volume : Measure Joint)) g
  change (∫ p, g p ∂Measure.map (pairedFrequencyEquiv A) volume) =
    ∫ p, g (pairedFrequencyEquiv A p) at h
  rw [map_pairedFrequency_volume,integral_smul_measure,ENNReal.toReal_ofReal (sq_nonneg _)] at h
  exact h.symm

/-- The manuscript's trilinear Fourier integrand, using the existing three
Fourier factors and allowing a complex scalar coefficient of a tensor symbol. -/
def radianTrilinearWeight (m : Joint → ℂ) (f g w : SchwartzMap Space ℂ) (p : Joint) : ℂ :=
  m p * radianWeight (fun _ => 1) f g w p

theorem radianTrilinearWeight_ofReal (m : Joint → ℝ) (f g w : SchwartzMap Space ℂ) :
    radianTrilinearWeight (fun p => (m p : ℂ)) f g w = radianWeight m f g w := by
  funext p
  simp only [radianTrilinearWeight,radianWeight,Complex.ofReal_one,one_mul,mul_assoc]

/-- The concrete two-frequency integral is absolutely integrable for a
bounded measurable scalar coefficient and Schwartz test factors. -/
theorem integrable_radianTrilinearWeight_of_bounded (m : Joint → ℂ)
    (hm : AEStronglyMeasurable m volume) (M : ℝ) (hM : ∀ p, ‖m p‖ ≤ M)
    (f g w : SchwartzMap Space ℂ) :
    Integrable (radianTrilinearWeight m f g w) := by
  let U (u : SchwartzMap Space ℂ) := SchwartzMap.fourierTransformCLM ℂ u
  have hτ : tau ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).ne'
  have hF (u : SchwartzMap Space ℂ) :
      radianFourier u = fun ξ => U u (tau⁻¹ • ξ) := by
    funext ξ
    dsimp only [U]
    rw [SchwartzMap.fourierTransformCLM_apply,← radianFourier_scaled,smul_smul,
      mul_inv_cancel₀ hτ,one_smul]
  have hf (u : SchwartzMap Space ℂ) : Integrable (radianFourier u) := by
    rw [hF]
    exact (U u).integrable.comp_smul (inv_ne_zero hτ)
  have hprod : Integrable (fun p : Joint => radianFourier f p.1 * radianFourier g p.2) := by
    rw [Measure.volume_eq_prod Space Space]
    exact (hf f).mul_prod (hf g)
  let b (p : Joint) := m p * radianFourier w (-(p.1+p.2))
  have hw : Continuous (fun p : Joint => radianFourier w (-(p.1+p.2))) := by
    rw [hF w]
    exact (U w).continuous.comp ((continuous_const_smul _).comp (continuous_fst.add continuous_snd).neg)
  have hb : AEStronglyMeasurable b volume := hm.mul hw.aestronglyMeasurable
  have hbound (p : Joint) : ‖b p‖ ≤ M * SchwartzMap.seminorm ℝ 0 0 (U w) := by
    rw [show b p = m p * U w (tau⁻¹ • (-(p.1+p.2))) by simp only [b,hF w],norm_mul]
    exact mul_le_mul (hM p) ((U w).norm_le_seminorm ℝ _) (norm_nonneg _)
      ((norm_nonneg _).trans (hM p))
  have eq (p : Joint) : radianTrilinearWeight m f g w p =
      b p * (radianFourier f p.1 * radianFourier g p.2) := by
    simp only [radianTrilinearWeight,radianWeight,Complex.ofReal_one,one_mul,b]
    ring
  rw [funext eq]
  exact hprod.bdd_mul hb ⟨_,hbound⟩

def radianTrilinearForm (m : Joint → ℂ) (f g w : SchwartzMap Space ℂ) : ℂ :=
  (tau^8)⁻¹ • ∫ p, radianTrilinearWeight m f g w p

/-- The physical factors on the normalized coordinates are f(A⁻ᵀ y). -/
def pullbackTrilinearFactor (A : Space ≃L[ℝ] Space) (f : SchwartzMap Space ℂ) : SchwartzMap Space ℂ :=
  pullbackSchwartz (physicalDualEquiv A).symm f

private theorem radianTrilinearWeight_pairedFrequency (A : Space ≃L[ℝ] Space) (m : Joint → ℂ)
    (f g w : SchwartzMap Space ℂ) :
    radianTrilinearWeight (m ∘ pairedFrequencyEquiv A) (pullbackTrilinearFactor A f)
        (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A w) =
      ((linearJacobian A)^3 : ℝ) • (radianTrilinearWeight m f g w ∘ pairedFrequencyEquiv A) := by
  have hF (u : SchwartzMap Space ℂ) (ζ : Space) :
      radianFourier (pullbackTrilinearFactor A u) ζ = linearJacobian A • radianFourier u (A ζ) :=
    radianFourier_comp_inverseDual A u ζ
  funext p
  change radianTrilinearWeight (m ∘ pairedFrequencyEquiv A) (pullbackTrilinearFactor A f)
        (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A w) p =
      ((linearJacobian A)^3 : ℝ) • radianTrilinearWeight m f g w (pairedFrequencyEquiv A p)
  simp only [radianTrilinearWeight,radianWeight,Function.comp_apply,pairedFrequencyEquiv_apply,
    Complex.ofReal_one,one_mul,hF,map_neg,map_add,Complex.real_smul,Complex.ofReal_pow]
  ring

/-- The exact signed third slot is preserved, and either integral is
absolutely integrable whenever the other is. -/
theorem integrable_radianTrilinearWeight_pairedFrequency_iff
    (A : Space ≃L[ℝ] Space) (m : Joint → ℂ) (f g w : SchwartzMap Space ℂ) :
    Integrable (radianTrilinearWeight (m ∘ pairedFrequencyEquiv A) (pullbackTrilinearFactor A f)
      (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A w)) ↔
      Integrable (radianTrilinearWeight m f g w) := by
  let e := (pairedFrequencyEquiv A).toHomeomorph.toMeasurableEquiv
  have hm : 0 < (linearJacobian A)⁻¹ ^ (2:ℕ) := pow_pos (inv_pos.mpr (linearJacobian_pos A)) _
  rw [radianTrilinearWeight_pairedFrequency,integrable_smul_iff (pow_ne_zero _ (linearJacobian_pos A).ne')]
  change Integrable (radianTrilinearWeight m f g w ∘ e) volume ↔ _
  rw [← e.measurableEmbedding.integrable_map_iff]
  change Integrable _ (Measure.map (pairedFrequencyEquiv A) volume) ↔ _
  rw [map_pairedFrequency_volume,integrable_smul_measure
    (ENNReal.ofReal_ne_zero_iff.mpr hm) ENNReal.ofReal_ne_top]

/-- Exact common change of variables in the original radian trilinear form. -/
theorem radianTrilinearForm_pairedFrequency (A : Space ≃L[ℝ] Space) (m : Joint → ℂ)
    (f g w : SchwartzMap Space ℂ) :
    radianTrilinearForm m f g w =
      (linearJacobian A)⁻¹ • radianTrilinearForm (m ∘ pairedFrequencyEquiv A)
        (pullbackTrilinearFactor A f) (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A w) := by
  let J := linearJacobian A
  have hJ : 0 < J := linearJacobian_pos A
  have hscale : J^3 * J⁻¹ ^ (2:ℕ) = J := by
    calc
      _ = J*(J*J⁻¹)^2 := by ring
      _ = J := by rw [mul_inv_cancel₀ hJ.ne',one_pow,mul_one]
  have h :
      radianTrilinearForm (m ∘ pairedFrequencyEquiv A) (pullbackTrilinearFactor A f)
        (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A w) =
        J • radianTrilinearForm m f g w := by
    unfold radianTrilinearForm
    rw [radianTrilinearWeight_pairedFrequency]
    change (tau^8)⁻¹ • (∫ p, J^3 • radianTrilinearWeight m f g w (pairedFrequencyEquiv A p)) =
      J • ((tau^8)⁻¹ • ∫ p, radianTrilinearWeight m f g w p)
    rw [integral_smul,integral_comp_pairedFrequency A,smul_smul (J^3) (J⁻¹ ^ (2:ℕ)),hscale,
      smul_comm ((tau^8)⁻¹) J]
  rw [h,smul_smul,inv_mul_cancel₀ hJ.ne',one_smul]

/-- A finite contracted component sum uses this same chart change in all slots. -/
theorem radianTrilinearForm_finite_contraction_pairedFrequency {ι : Type*} [Fintype ι]
    (A : Space ≃L[ℝ] Space) (m : ι → Joint → ℂ) (f g w : ι → SchwartzMap Space ℂ) :
    (∑ i, radianTrilinearForm (m i) (f i) (g i) (w i)) =
      (linearJacobian A)⁻¹ • ∑ i, radianTrilinearForm (m i ∘ pairedFrequencyEquiv A)
        (pullbackTrilinearFactor A (f i)) (pullbackTrilinearFactor A (g i)) (pullbackTrilinearFactor A (w i)) := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => radianTrilinearForm_pairedFrequency A (m i) (f i) (g i) (w i))

end Burnett.Analysis.CapFourier
