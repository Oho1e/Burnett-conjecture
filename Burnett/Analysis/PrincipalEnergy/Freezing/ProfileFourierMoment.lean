import Burnett.Analysis.PrincipalEnergy.Freezing.ModulatedAngularAction
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace Burnett.A03

open MeasureTheory Burnett.A02.FrequencySplit
open scoped FourierTransform RealInnerProductSpace

/-- Absolute Fourier moment in the spatial frequency convention used by the
left-action and commutator integrals. -/
def patchFourierMoment (r : ℕ) (f : E → ℂ) : ℝ :=
  ∫ η, ‖η‖ ^ r * ‖𝓕 f η‖

private theorem fourier_phase_change (η x : E) :
    Complex.exp ((↑(-2 * Real.pi * ⟪x, η⟫) : ℂ) * Complex.I) = patchFourierPhase (-η) x := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, inner_neg_left, real_inner_comm η x]
  have h : (-2 : ℝ) * Real.pi * ⟪η, x⟫ = 2 * Real.pi * (-⟪η, x⟫) := by ring
  exact congrArg (fun t : ℝ => Complex.exp ((t : ℂ) * Complex.I)) h

private theorem fourier_phase_spatial_add (η x y : E) :
    patchFourierPhase η (x + y) = patchFourierPhase η x * patchFourierPhase η y := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, inner_add_right, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]

private theorem fourier_phase_scale (η x : E) (ℓ : ℝ) :
    patchFourierPhase η (ℓ • x) = patchFourierPhase (ℓ • η) x := by
  simp only [Burnett.Microlocal.Overlap.baseFourierPhase, real_inner_smul_left, real_inner_smul_right]

/-- Exact affine change of coordinates for the actual complex Fourier transform.
The center enters only through a unit complex phase. -/
theorem patch_fourier_affine (f : E → ℂ) (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ) (η : E) :
    𝓕 (fun x : E => f (ℓ⁻¹ • (x - c))) η =
      ℓ ^ Module.finrank ℝ E • (patchFourierPhase (-η) c * 𝓕 f (ℓ • η)) := by
  rw [Real.fourierIntegral_eq', Real.fourierIntegral_eq']
  simp only [smul_eq_mul, fourier_phase_change]
  let H (y : E) := patchFourierPhase (-η) (ℓ • y + c) * f y
  have eq : (fun x : E => patchFourierPhase (-η) x * f (ℓ⁻¹ • (x - c))) =
      fun x : E => H (ℓ⁻¹ • (x + -c)) := by
    funext x
    dsimp only [H]
    rw [← sub_eq_add_neg, smul_smul, mul_inv_cancel₀ hℓ.ne', one_smul, sub_add_cancel]
  rw [eq, integral_add_right_eq_self (fun x : E => H (ℓ⁻¹ • x)) (-c)]
  rw [Measure.integral_comp_inv_smul_of_nonneg (volume : Measure E) H hℓ.le, ← integral_const_mul]
  congr 1
  apply integral_congr_ae
  filter_upwards with y
  simp only [H, fourier_phase_spatial_add, mul_assoc, fourier_phase_scale, smul_neg]
  ring

/-- The Fourier moment of an affine rescaling has the exact inverse length
power. Consequently its estimate is uniform in the patch center. -/
theorem patch_fourier_moment_affine (r : ℕ) (f : E → ℂ) (c : E) (ℓ : ℝ) (hℓ : 0 < ℓ) :
    patchFourierMoment r (fun x => f (ℓ⁻¹ • (x - c))) =
      (ℓ ^ r)⁻¹ * patchFourierMoment r f := by
  let M (η : E) := ‖η‖ ^ r * ‖𝓕 f η‖
  unfold patchFourierMoment
  simp_rw [patch_fourier_affine f c ℓ hℓ, norm_smul, norm_mul, patch_fourier_phase_norm, one_mul,
    Real.norm_of_nonneg (pow_nonneg hℓ.le _)]
  have pointwise (η : E) :
      ‖η‖ ^ r * (ℓ ^ Module.finrank ℝ E * ‖𝓕 f (ℓ • η)‖) =
        (ℓ ^ r)⁻¹ * (ℓ ^ Module.finrank ℝ E) * M (ℓ • η) := by
    dsimp only [M]
    rw [norm_smul, Real.norm_of_nonneg hℓ.le, mul_pow]
    field_simp [hℓ.ne']
  simp_rw [pointwise]
  rw [integral_const_mul, Measure.integral_comp_smul_of_nonneg (volume : Measure E) M ℓ (hR := hℓ.le)]
  rw [smul_eq_mul]
  change ((ℓ ^ r)⁻¹ * ℓ ^ Module.finrank ℝ E) *
      ((ℓ ^ Module.finrank ℝ E)⁻¹ * ∫ η, M η) = (ℓ ^ r)⁻¹ * ∫ η, M η
  field_simp [hℓ.ne']

end Burnett.A03
