import Burnett.Analysis.CubicEnergy.CompleteEnergy.PhysicalCommutator
import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianDegreeOne

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.Fourier Burnett.RicciSymbol
open Burnett.Microlocal.AngularCommutator
open scoped ContDiff FourierTransform ComplexConjugate RealInnerProductSpace

private theorem order_one_radian_spectrum_integrable (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f : SchwartzMap E ℂ) :
    Integrable (radianActionSpectrum b f) := by
  let B : E → ℝ := fun x => b (tau • x)
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hB : ContDiffOn ℝ ∞ B {x | x ≠ 0} :=
    hb.comp (contDiff_const.smul contDiff_id).contDiffOn (fun _ hx => smul_ne_zero ht.ne' hx)
  have hHom : ∀ t : ℝ, 0 < t → ∀ x, B (t • x) = t * B x := by
    intro t h x
    change b (tau • (t • x)) = t * b (tau • x)
    rw [smul_comm tau t x, hom t h]
  exact orderOne_spectrum_integrable B hB hHom f

private theorem inverse_spectrum_pairing (F : E → ℂ) (hF : Integrable F) (g : SchwartzMap E ℂ) :
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

/-- The actual order-one multiplier on a Schwartz input has its frequency
pairing against every Schwartz test under the radian normalization. -/
theorem radian_order_one_pairing (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f g : SchwartzMap E ℂ) :
    (∫ x, radianAction b f x * conj (g x)) =
      ∫ ξ, radianActionSpectrum b f ξ * conj (𝓕 (g : E → ℂ) ξ) := by
  simp_rw [← radianActionSpectrum_inverse]
  exact inverse_spectrum_pairing _ (order_one_radian_spectrum_integrable b hb hom f) g

private theorem radian_order_one_pairing_right (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f g : SchwartzMap E ℂ) :
    (∫ x, f x * conj (radianAction b g x)) =
      ∫ ξ, 𝓕 (f : E → ℂ) ξ * conj (radianActionSpectrum b g ξ) := by
  have eq := congrArg (starRingEnd ℂ) (radian_order_one_pairing b hb hom g f)
  rw [← integral_conj, ← integral_conj] at eq
  simpa only [map_mul, starRingEnd_self_apply, mul_comm] using eq

/-- A real order-one symbol yields the self-adjoint pairing needed for the
complete quasilinear energy. Both physical arguments are Schwartz before
application of the multiplier. -/
theorem radian_order_one_self_adjoint (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x) (f g : SchwartzMap E ℂ) :
    (∫ x, radianAction b f x * conj (g x)) = ∫ x, f x * conj (radianAction b g x) := by
  rw [radian_order_one_pairing b hb hom, radian_order_one_pairing_right b hb hom]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [radianActionSpectrum, map_mul, Complex.conj_ofReal]
  ring

/-- Coordinate differentiation of a Schwartz function, with no factor of i. -/
def energyPartial (j : Index) (f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  SchwartzMap.pderivCLM ℂ (EuclideanSpace.single j 1) f

theorem energyPartial_fourier (j : Index) (f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (energyPartial j f : E → ℂ) ξ =
      ((tau * ξ j : ℝ) : ℂ) * Complex.I * 𝓕 (f : E → ℂ) ξ := by
  unfold energyPartial
  rw [Burnett.Analysis.HminusWeightedDual.fourier_pderiv f]
  simp only [EuclideanSpace.inner_single_right, conj_trivial, tau,
    Complex.ofReal_mul]
  push_cast
  ring

/-- Weak integration by parts moves the actual derivative through the
order-one Fourier multiplier in the physical pairing. -/
theorem radian_order_one_partial_pairing (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0})
    (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (j : Index) (f g : SchwartzMap E ℂ) :
    (∫ x, energyPartial j f x * conj (radianAction b g x)) =
      -∫ x, f x * conj (radianAction b (energyPartial j g) x) := by
  rw [radian_order_one_pairing_right b hb hom, radian_order_one_pairing_right b hb hom, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with ξ
  simp only [radianActionSpectrum, energyPartial_fourier, map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

end Burnett.A02.FrequencySplit
