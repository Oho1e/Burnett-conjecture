import Burnett.Analysis.Microlocal.AuxiliaryAmplitudeCovariance

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.FixedChartGeometricDensity

open Matrix Burnett.RicciSymbol Burnett.Microlocal.CurlDensity
open scoped BigOperators Matrix

/-- Positive change of scale from a round covector to the auxiliary unit covector. -/
def auxiliaryScale (rInv : Tensor2) (ξ : Covector) : ℝ :=
  (Real.sqrt (symbolNorm rInv ξ))⁻¹

def auxiliaryUnitCovector (rInv : Tensor2) (ξ : Covector) : Covector :=
  fun a => auxiliaryScale rInv ξ * ξ a

theorem auxiliaryScale_pos (rInv : Tensor2) (ξ : Covector) (h : 0 < symbolNorm rInv ξ) :
    0 < auxiliaryScale rInv ξ :=
  inv_pos.mpr (Real.sqrt_pos.mpr h)

theorem symbolNorm_rescale (rInv : Tensor2) (ξ : Covector) (scale : ℝ) :
    symbolNorm rInv (fun a => scale * ξ a) = scale ^ 2 * symbolNorm rInv ξ := by
  simp only [symbolNorm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem auxiliaryUnitCovector_unit (rInv : Tensor2) (ξ : Covector) (h : 0 < symbolNorm rInv ξ) :
    symbolNorm rInv (auxiliaryUnitCovector rInv ξ) = 1 := by
  change symbolNorm rInv (fun a => auxiliaryScale rInv ξ * ξ a) = 1
  rw [symbolNorm_rescale, auxiliaryScale, inv_pow,
    Real.sq_sqrt h.le, inv_mul_cancel₀ h.ne']

theorem auxiliaryUnitCovector_same_ray (rInv : Tensor2) (ξ : Covector) (h : 0 < symbolNorm rInv ξ) :
    ∃ scale : ℝ, 0 < scale ∧ ∀ a, auxiliaryUnitCovector rInv ξ a = scale * ξ a :=
  ⟨auxiliaryScale rInv ξ, auxiliaryScale_pos rInv ξ h, fun _ => rfl⟩

theorem curlMatrix_rescale (ξ : Covector) (scale : ℝ) :
    curlMatrix (fun a => scale * ξ a) = (scale : ℂ) • curlMatrix ξ := by
  ext i j
  simp only [curlMatrix, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  split_ifs <;> ring

theorem ricciJetMatrix_rescale (G : Tensor2) (ξ : Covector) (scale : ℝ) :
    ricciJetMatrix G (fun a => scale * ξ a) = (scale : ℂ) • ricciJetMatrix G ξ := by
  ext i j
  simp only [ricciJetMatrix, LinearMap.toMatrix'_apply, ricciJetLinear_apply,
    ricciJetSymbol, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

theorem gradientEmbedding_rescale (ξ : Covector) (scale : ℝ) :
    gradientEmbedding (fun a => scale * ξ a) = (scale : ℂ) • gradientEmbedding ξ := by
  ext i j
  simp only [gradientEmbedding, Matrix.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  split_ifs <;> ring

/-- The same ordered jet covariance contracted using the round dual. -/
def roundAmplitudeCovariance (ξ : Covector) (M : Matrix JetSlot JetSlot ℂ) :
    Matrix Pair Pair ℂ :=
  let C := gradientContraction ξ
  C * M * Cᴴ

theorem roundAmplitudeCovariance_of_rescaled_factorization (ξ : Covector)
    (hround : ∑ a, ξ a * ξ a = 1) (scale : ℝ)
    (M : Matrix JetSlot JetSlot ℂ) (S : Matrix Pair Pair ℂ)
    (hM : M = gradientEmbedding (fun a => scale * ξ a) * S *
      (gradientEmbedding (fun a => scale * ξ a))ᴴ) :
    roundAmplitudeCovariance ξ M = (scale : ℂ) ^ 2 • S := by
  let J := gradientEmbedding ξ
  let C := gradientContraction ξ
  change C * M * Cᴴ = _
  rw [hM, gradientEmbedding_rescale, Matrix.conjTranspose_smul, Complex.star_def,
    Complex.conj_ofReal]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, ← pow_two]
  change (scale : ℂ) ^ 2 • (C * (J * S * Jᴴ) * Cᴴ) = _
  rw [amplitudeCovariance_unique ξ ξ hround S]

theorem auxiliary_factorization_amplitude_scale (rInv : Tensor2) (ξ : Covector)
    (hround : ∑ a, ξ a * ξ a = 1) (h : 0 < symbolNorm rInv ξ)
    (M : Matrix JetSlot JetSlot ℂ)
    (hM : M = gradientEmbedding (auxiliaryUnitCovector rInv ξ) *
      auxiliaryAmplitudeCovariance rInv (auxiliaryUnitCovector rInv ξ) M *
      (gradientEmbedding (auxiliaryUnitCovector rInv ξ))ᴴ) :
    auxiliaryAmplitudeCovariance rInv (auxiliaryUnitCovector rInv ξ) M =
      ((((auxiliaryScale rInv ξ) ^ 2)⁻¹ : ℝ) : ℂ) • roundAmplitudeCovariance ξ M := by
  let scale := auxiliaryScale rInv ξ
  let S := auxiliaryAmplitudeCovariance rInv (auxiliaryUnitCovector rInv ξ) M
  have h0 : (scale : ℂ) ^ 2 ≠ 0 :=
    pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (auxiliaryScale_pos rInv ξ h).ne')
  have hscale := roundAmplitudeCovariance_of_rescaled_factorization ξ hround scale M S hM
  have hscaled := congrArg (fun A : Matrix Pair Pair ℂ => ((scale : ℂ) ^ 2)⁻¹ • A) hscale
  dsimp only at hscaled
  rw [smul_smul, inv_mul_cancel₀ h0, one_smul] at hscaled
  change S = (((scale ^ 2)⁻¹ : ℝ) : ℂ) • roundAmplitudeCovariance ξ M
  rw [Complex.ofReal_inv, Complex.ofReal_pow]
  exact hscaled.symm

end Burnett.Microlocal.FixedChartGeometricDensity
