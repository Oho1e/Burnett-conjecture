import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency
import Burnett.Analysis.H1FourierEnergy

set_option autoImplicit false

noncomputable section

namespace Burnett.A07

open Burnett.A02.FrequencySplit (E radianFourier radianFourier_scaled tau)
open scoped FourierTransform

/-- The actual partial derivative of a Schwartz field in one of the four coordinates. -/
def coordinateDerivative (a : Fin 4) : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.pderivCLM ℂ (EuclideanSpace.single a 1)

private theorem tau_positive : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private theorem tau_smul_inv_smul (p : E) : tau • (tau⁻¹ • p) = p := by
  rw [smul_smul, mul_inv_cancel₀ tau_positive.ne', one_smul]

/-- Coordinate differentiation in the radian normalization multiplies a
Schwartz spectrum by i times that frequency coordinate. -/
theorem radianFourier_coordinateDerivative (a : Fin 4) (f : SchwartzMap E ℂ) (p : E) :
    radianFourier (coordinateDerivative a f) p =
      Complex.I * (p a : ℂ) * radianFourier f p := by
  have hrescale (v : E → ℂ) :
      𝓕 v (tau⁻¹ • p) = radianFourier v p := by
    rw [← radianFourier_scaled, tau_smul_inv_smul]
  have hunit : (tau : ℂ) * ((tau⁻¹ : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, mul_inv_cancel₀ tau_positive.ne', Complex.ofReal_one]
  rw [← hrescale (coordinateDerivative a f), coordinateDerivative,
    Burnett.Analysis.HminusWeightedDual.fourier_pderiv, EuclideanSpace.inner_single_right]
  simp only [one_mul, conj_trivial, hrescale]
  rw [PiLp.smul_apply, smul_eq_mul,
    show (2 : ℂ) * (Real.pi : ℂ) = (tau : ℂ) by norm_num [tau]]
  have hcast : ((tau⁻¹ * p a : ℝ) : ℂ) = ((tau⁻¹ : ℝ) : ℂ) * (p a : ℂ) :=
    Complex.ofReal_mul _ _
  rw [hcast]
  calc
    _ = ((tau : ℂ) * ((tau⁻¹ : ℝ) : ℂ)) *
        (Complex.I * (p a : ℂ) * radianFourier f p) := by ac_rfl
    _ = _ := by rw [hunit, one_mul]

end Burnett.A07
