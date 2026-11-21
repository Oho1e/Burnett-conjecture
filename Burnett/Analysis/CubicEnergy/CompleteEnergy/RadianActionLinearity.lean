import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory
open scoped ContDiff FourierTransform RealInnerProductSpace

private theorem degree_one_radian_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0<t → ∀ ξ, b (t • ξ) = t*b ξ)
    (f : SchwartzMap E ℂ) : Integrable (radianActionSpectrum b f) := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have eq : radianActionSpectrum b f = fun ξ => (tau : ℂ) * ((b ξ : ℂ) * 𝓕 (f : E → ℂ) ξ) := by
    funext ξ
    simp only [radianActionSpectrum, hom tau ht, Complex.ofReal_mul, mul_assoc]
  rw [eq]
  exact (orderOne_spectrum_integrable b hb hom f).const_mul _

theorem radian_action_add (b : E → ℝ) (hb : ContDiffOn ℝ ∞ b {ξ | ξ ≠ 0})
    (hom : ∀ t : ℝ, 0<t → ∀ ξ, b (t • ξ) = t*b ξ) (f g : SchwartzMap E ℂ) :
    radianAction b (f+g) = radianAction b f + radianAction b g := by
  have eq : radianActionSpectrum b (f+g) = radianActionSpectrum b f + radianActionSpectrum b g := by
    funext ξ
    change (b (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ (f+g)) ξ =
      (b (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ f) ξ +
        (b (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ g) ξ
    simp only [map_add, SchwartzMap.add_apply, mul_add]
  simp only [← radianActionSpectrum_inverse, eq]
  exact VectorFourier.fourierIntegral_add (L := -(innerₗ E)) Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd).neg (degree_one_radian_integrable b hb hom f)
    (degree_one_radian_integrable b hb hom g)

theorem radian_action_real_smul (b : E → ℝ) (c : ℝ) (f : SchwartzMap E ℂ) :
    radianAction b (c • f) = c • radianAction b f := by
  have input : c • f = (c : ℂ) • f := by
    ext x
    simp only [SchwartzMap.smul_apply, Complex.real_smul, smul_eq_mul]
  have eq : radianActionSpectrum b (c • f) = (c : ℂ) • radianActionSpectrum b f := by
    rw [input]
    funext ξ
    change (b (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ ((c : ℂ) • f)) ξ =
      (c : ℂ) * ((b (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ f) ξ)
    simp only [map_smul, SchwartzMap.smul_apply, smul_eq_mul]
    ring
  calc
    _ = 𝓕⁻ ((c : ℂ) • radianActionSpectrum b f) := by
      rw [← radianActionSpectrum_inverse, eq]
    _ = (c : ℂ) • 𝓕⁻ (radianActionSpectrum b f) :=
      VectorFourier.fourierIntegral_const_smul Real.fourierChar volume (-(innerₗ E)) _ _
    _ = _ := by
      rw [radianActionSpectrum_inverse]
      funext x
      exact Complex.real_smul.symm

end Burnett.A02.FrequencySplit
