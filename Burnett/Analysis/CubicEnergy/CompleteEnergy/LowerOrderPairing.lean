import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianActionLinearity

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff FourierTransform ComplexConjugate RealInnerProductSpace ENNReal

private theorem inverse_integrable_spectrum_pairing (F : E → ℂ) (hF : Integrable F) (g : SchwartzMap E ℂ) :
    (∫ x, (𝓕⁻ F) x * conj (g x)) = ∫ ξ, F ξ * conj (𝓕 (g : E → ℂ) ξ) := by
  let C := fun x : E => conj (g x)
  have hc : Continuous C := Complex.continuous_conj.comp g.continuous
  have ic : Integrable C := g.integrable.norm.mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simp [C])
  calc
    _ = 𝓕 (fun x => C x * (𝓕⁻ F) x) 0 := by
      rw [Real.fourierIntegral_eq']
      simp [C, mul_comm]
    _ = ∫ ξ, 𝓕 C (0 - ξ) * F ξ := fourier_mul_inverse_eq_integral C F ic hF 0
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with ξ
      change 𝓕 (fun x => conj (g x)) (0 - ξ) * F ξ = _
      rw [zero_sub, fourier_conj_eq_conj_inverse, Real.fourierIntegralInv_eq_fourierIntegral_neg,
        neg_neg, mul_comm]

/-- The weak pairing of an actual radian action only needs its integrable
spectrum. The symbol can be singular at the origin. -/
theorem radian_pairing_right_of_integrable_spectrum (m : E → ℝ) (f g : SchwartzMap E ℂ)
    (hg : Integrable (radianActionSpectrum m g)) :
    (∫ x, f x * conj (radianAction m g x)) =
      ∫ ξ, 𝓕 (f : E → ℂ) ξ * conj (radianActionSpectrum m g ξ) := by
  have eq := congrArg (starRingEnd ℂ) (inverse_integrable_spectrum_pairing _ hg f)
  rw [← integral_conj,← integral_conj] at eq
  simpa only [radianActionSpectrum_inverse, map_mul, starRingEnd_self_apply, mul_comm] using eq

theorem radian_partial_pairing_of_integrable_spectrum (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (j : Index) (f g : SchwartzMap E ℂ) :
    (∫ x, energyPartial j f x * conj (radianAction m g x)) =
      -∫ x, f x * conj (radianAction m (energyPartial j g) x) := by
  rw [radian_pairing_right_of_integrable_spectrum m _ _ (spectrum _),
    radian_pairing_right_of_integrable_spectrum m _ _ (spectrum _), ← integral_neg]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [radianActionSpectrum, energyPartial_fourier, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem radian_action_add_of_integrable_spectra (m : E → ℝ) (f g : SchwartzMap E ℂ)
    (hf : Integrable (radianActionSpectrum m f)) (hg : Integrable (radianActionSpectrum m g)) :
    radianAction m (f+g) = radianAction m f + radianAction m g := by
  have eq : radianActionSpectrum m (f+g) = radianActionSpectrum m f + radianActionSpectrum m g := by
    funext ξ
    change (m (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ (f+g)) ξ =
      (m (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ f) ξ +
        (m (tau • ξ) : ℂ) * (SchwartzMap.fourierTransformCLM ℂ g) ξ
    simp only [map_add, SchwartzMap.add_apply, mul_add]
  simp only [← radianActionSpectrum_inverse, eq]
  exact VectorFourier.fourierIntegral_add (L := -(innerₗ E)) Real.continuous_fourierChar
    (continuous_fst.inner continuous_snd).neg hf hg

theorem radian_test_integrable_of_L3 (m : E → ℝ)
    (f g : SchwartzMap E ℂ) (hg : MemLp (radianAction m g) (ENNReal.ofReal 3) volume) :
    Integrable (fun x => f x * conj (radianAction m g x)) := by
  have h : (3 / 2 : ℝ).HolderTriple 3 1 := ⟨by norm_num, by norm_num, by norm_num⟩
  letI : ENNReal.HolderTriple (ENNReal.ofReal (3 / 2)) (ENNReal.ofReal 3) (ENNReal.ofReal 1) :=
    h.ennrealOfReal
  let Z := fun x => conj (radianAction m g x)
  have hz : MemLp Z (ENNReal.ofReal 3) volume :=
    hg.congr_norm (Complex.continuous_conj.comp_aestronglyMeasurable hg.1)
      (Filter.Eventually.of_forall fun x => by simp [Z])
  have mem : MemLp (fun x => f x * Z x) (ENNReal.ofReal 1) volume :=
    hz.mul' (f.memLp (ENNReal.ofReal (3 / 2)) volume)
  exact memLp_one_iff_integrable.mp (by simpa only [ENNReal.ofReal_one] using mem)

/-- Move one derivative of the exact quasilinear term through the physical
test, using the same actual Fourier multiplier on the differentiated test. -/
theorem quasilinear_component_ibp_of_integrable_spectrum (m : E → ℝ)
    (spectrum : ∀ g : SchwartzMap E ℂ, Integrable (radianActionSpectrum m g))
    (mem : ∀ g : SchwartzMap E ℂ, MemLp (radianAction m g) (ENNReal.ofReal 3) volume)
    (a d : Index) (A u v : SchwartzMap E ℂ) :
    (∫ x, A x * energyPartial a (energyPartial d u) x * conj (radianAction m v x)) =
      -(∫ x, A x * energyPartial d u x * conj (radianAction m (energyPartial a v) x)) -
      ∫ x, energyPartial a A x * energyPartial d u x * conj (radianAction m v x) := by
  let U := energyPartial d u
  have main := radian_partial_pairing_of_integrable_spectrum m spectrum a (energyProduct A U) v
  have first := radian_test_integrable_of_L3 m (energyProduct A (energyPartial a U)) v (mem v)
  have second := radian_test_integrable_of_L3 m (energyProduct (energyPartial a A) U) v (mem v)
  simp only [energyProduct_apply] at first second
  have terms (x : E) :
      energyPartial a (energyProduct A U) x * conj (radianAction m v x) =
        A x * energyPartial a U x * conj (radianAction m v x) +
          energyPartial a A x * U x * conj (radianAction m v x) := by
    rw [energyPartial_product]
    ring
  simp_rw [terms] at main
  rw [integral_add first second] at main
  simpa only [energyProduct_apply, U] using eq_sub_of_add_eq main

theorem fixed_profile_spectrum_integrable (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (f : SchwartzMap E ℂ) :
    Integrable (radianActionSpectrum (fixedRadianProfile a) f) := by
  have eq : radianActionSpectrum (fixedRadianProfile a) f = fun ξ => a ξ * 𝓕 (f : E → ℂ) ξ := by
    funext ξ
    simp only [radianActionSpectrum,fixedRadianProfile_scaled,areal]
  rw [eq]
  exact (SchwartzMap.fourierTransformCLE ℂ f).integrable.bdd_mul a.continuous.aestronglyMeasurable
    ⟨_, SchwartzMap.norm_le_seminorm ℝ a⟩

private theorem homogeneous_radian_spectrum_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (f : SchwartzMap E ℂ) : Integrable (radianActionSpectrum b f) := by
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have eq : radianActionSpectrum b f = fun ξ => (tau : ℂ) * ((b ξ : ℂ) * 𝓕 (f : E → ℂ) ξ) := by
    funext ξ
    simp only [radianActionSpectrum, hom tau ht, Complex.ofReal_mul, mul_assoc]
  rw [eq]
  exact (orderOne_spectrum_integrable b hb hom f).const_mul _

theorem fixed_cut_spectrum_integrable (a : SchwartzMap E ℂ)
    (areal : ∀ ξ, ((a ξ).re : ℂ) = a ξ) (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0<t → ∀ x, b (t • x) = t*b x)
    (f : SchwartzMap E ℂ) :
    Integrable (radianActionSpectrum (fun ζ => fixedRadianProfile a ζ * b ζ) f) := by
  have eq : radianActionSpectrum (fun ζ => fixedRadianProfile a ζ * b ζ) f =
      fun ξ => a ξ * radianActionSpectrum b f ξ := by
    funext ξ
    simp only [radianActionSpectrum, fixedRadianProfile_scaled, Complex.ofReal_mul, areal, mul_assoc]
  rw [eq]
  exact (homogeneous_radian_spectrum_integrable b hb hom f).bdd_mul a.continuous.aestronglyMeasurable
    ⟨_, SchwartzMap.norm_le_seminorm ℝ a⟩

end Burnett.A02.FrequencySplit
