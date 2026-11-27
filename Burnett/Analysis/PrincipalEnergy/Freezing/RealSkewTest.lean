import Burnett.Analysis.CubicEnergy.CompleteEnergy.RadianOrderOnePairing

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open MeasureTheory Burnett.Fourier
open scoped FourierTransform ComplexConjugate ContDiff

/-- The Fourier test used in the freezing lemma, with the paper's sign. -/
def radianSkewAction (b : E → ℝ) (f : SchwartzMap E ℂ) (x : E) : ℂ :=
  -Complex.I * radianAction b f x

private theorem conjugate_odd_action (b : E → ℝ) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x) (x : E) :
    conj (radianAction b f x) = -radianAction b f x := by
  let S := radianActionSpectrum b f
  have feq : (fun x => conj (f x)) = (f : E → ℂ) := funext hf
  have fourier_real (ξ : E) : conj (𝓕 (f : E → ℂ) ξ) = 𝓕 (f : E → ℂ) (-ξ) := by
    have eq := fourier_conj_eq_conj_inverse (f : E → ℂ) (-ξ)
    rw [feq, Real.fourierIntegralInv_eq_fourierIntegral_neg, neg_neg] at eq
    exact eq.symm
  have spectrum (ξ : E) : conj (S ξ) = -S (-ξ) := by
    simp only [S, radianActionSpectrum, map_mul, Complex.conj_ofReal, fourier_real,
      smul_neg, hodd, Complex.ofReal_neg, neg_mul, neg_neg]
  rw [← radianActionSpectrum_inverse b f]
  change conj (𝓕⁻ S x) = -𝓕⁻ S x
  calc
    _ = 𝓕 (fun ξ => conj (S ξ)) x := (fourier_conj_eq_conj_inverse S x).symm
    _ = 𝓕 (fun ξ => -S (-ξ)) x := by simp_rw [spectrum]
    _ = -𝓕 (fun ξ => S (-ξ)) x := by
      rw [Real.fourierIntegral_eq', Real.fourierIntegral_eq']
      simp only [smul_neg, integral_neg]
    _ = _ := by rw [Real.fourierIntegralInv_eq_fourierIntegral_comp_neg]

/-- A real odd symbol makes the actual Q test preserve pointwise real fields. -/
theorem radianSkewAction_preserves_real (b : E → ℝ) (hodd : ∀ ξ, b (-ξ) = -b ξ)
    (f : SchwartzMap E ℂ) (hf : ∀ x, conj (f x) = f x) (x : E) :
    conj (radianSkewAction b f x) = radianSkewAction b f x := by
  simp only [radianSkewAction, map_mul, map_neg, Complex.conj_I, neg_neg,
    conjugate_odd_action b hodd f hf x, mul_neg, neg_mul]

/-- Skew-adjointness of the actual Q test in the Hermitian pairing, with
the first slot linear as in the freezing proof. -/
theorem radianSkewAction_skew_adjoint (b : E → ℝ)
    (hb : ContDiffOn ℝ ∞ b {x | x ≠ 0}) (hom : ∀ t : ℝ, 0 < t → ∀ x, b (t • x) = t * b x)
    (f g : SchwartzMap E ℂ) :
    (∫ x, radianSkewAction b f x * conj (g x)) =
      -∫ x, f x * conj (radianSkewAction b g x) := by
  calc
    _ = -Complex.I * ∫ x, radianAction b f x * conj (g x) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      simp only [radianSkewAction, mul_assoc]
    _ = -Complex.I * ∫ x, f x * conj (radianAction b g x) := by
      rw [radian_order_one_self_adjoint b hb hom f g]
    _ = _ := by
      rw [← integral_const_mul, ← integral_neg]
      apply integral_congr_ae
      filter_upwards with x
      simp only [radianSkewAction, map_mul, map_neg, Complex.conj_I, neg_neg]
      ring

end Burnett.A02.FrequencySplit
