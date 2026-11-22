import Burnett.Analysis.GaugeProjection.GaugeProjectionSymbol
import Burnett.Analysis.Fourier.RadianCoordinateDerivative

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.P01

open Matrix
open Burnett.A02.FrequencySplit (E radianFourier radianFourier_scaled tau)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped BigOperators FourierTransform Matrix

abbrev ComplexCovector := Fin 4 → ℂ
abbrev ComplexComponents := Matrix (Fin 4) (Fin 4) ℂ

private def complexFrequency (ξ : E) : ComplexCovector := fun i => (ξ i : ℂ)

private def complexDirectionProjection (ξ : E) : ComplexComponents :=
  (directionProjection (fun i => ξ i)).map Complex.ofReal

private theorem complexDirectionProjection_transpose (ξ : E) :
    (complexDirectionProjection ξ)ᵀ = complexDirectionProjection ξ := by
  rw [complexDirectionProjection, ← transpose_map, directionProjection_transpose]

private theorem complexDirectionProjection_kills (ξ : E) :
    complexDirectionProjection ξ *ᵥ complexFrequency ξ = 0 := by
  let x : Covector := fun j => ξ j
  have hx : directionProjection x *ᵥ x = 0 := by
    by_cases h : x = 0
    · simp [h]
    · exact directionProjection_kills_covector h
  funext a
  have ha := congrArg Complex.ofReal (congrFun hx a)
  simpa only [complexDirectionProjection, complexFrequency, x, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Pi.zero_apply, Complex.ofReal_zero, Complex.ofReal_sum, Complex.ofReal_mul] using ha

/-- Complex-linear action of the real, infrared-regularized matrix symbol. -/
def regularizedComplexGaugeProjection (ξ : E) (H : ComplexComponents) : ComplexComponents :=
  (gaugeProjectionInfrared ‖ξ‖ : ℂ) •
    (complexDirectionProjection ξ * H * complexDirectionProjection ξ)

theorem regularizedComplexGaugeProjection_apply (ξ : E) (H : ComplexComponents)
    (a b : Fin 4) :
    regularizedComplexGaugeProjection ξ H a b =
      ∑ c, ∑ d, (regularizedGaugeProjectionSymbol a b c d ξ : ℂ) * H c d := by
  simp only [regularizedComplexGaugeProjection, regularizedGaugeProjectionSymbol, gaugeProjectionSymbol,
    complexDirectionProjection, directionProjectionEntry, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.map_apply, Complex.ofReal_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  ring

/-- Exact pointwise annihilation also holds on complex Fourier amplitudes. -/
theorem regularizedComplexGaugeProjection_kills (ξ : E) (v : ComplexCovector) :
    regularizedComplexGaugeProjection ξ
      (vecMulVec (complexFrequency ξ) v + vecMulVec v (complexFrequency ξ)) = 0 := by
  have hr : complexFrequency ξ ᵥ* complexDirectionProjection ξ = 0 := by
    rw [← mulVec_transpose, complexDirectionProjection_transpose, complexDirectionProjection_kills]
  simp only [regularizedComplexGaugeProjection, mul_add, add_mul, mul_vecMulVec,
    complexDirectionProjection_kills, vecMulVec_mul, hr]
  simp

private theorem radianFourier_addSchwartz (f g : SchwartzMap E ℂ) (ξ : E) :
    radianFourier (f + g : SchwartzMap E ℂ) ξ = radianFourier f ξ + radianFourier g ξ := by
  let x := tau⁻¹ • ξ
  have ht : tau ≠ 0 := (mul_pos (show (0 : ℝ) < 2 by norm_num) Real.pi_pos).ne'
  have hx : tau • x = ξ := by
    dsimp only [x]
    rw [smul_smul, mul_inv_cancel₀ ht, one_smul]
  rw [← hx, radianFourier_scaled, radianFourier_scaled, radianFourier_scaled]
  change (SchwartzMap.fourierTransformCLM ℂ (f + g)) x =
    (SchwartzMap.fourierTransformCLM ℂ f) x + (SchwartzMap.fourierTransformCLM ℂ g) x
  rw [map_add]
  rfl

/-- The regularized projection annihilates the actual radian spectrum of a
symmetrized gradient of Schwartz covector fields. -/
theorem regularizedComplexGaugeProjection_symmetrizedGradient
    (V : Fin 4 → SchwartzMap E ℂ) (ξ : E) :
    regularizedComplexGaugeProjection ξ
      (fun a b => radianFourier (coordinateDerivative a (V b) + coordinateDerivative b (V a) :
        SchwartzMap E ℂ) ξ) = 0 := by
  let v : ComplexCovector := fun j => radianFourier (V j) ξ
  have eq : (fun a b => radianFourier
      (coordinateDerivative a (V b) + coordinateDerivative b (V a) : SchwartzMap E ℂ) ξ) =
    (Complex.I • (vecMulVec (complexFrequency ξ) v + vecMulVec v (complexFrequency ξ)) : ComplexComponents) := by
    ext a b
    simp only [radianFourier_addSchwartz, radianFourier_coordinateDerivative, Matrix.smul_apply, smul_eq_mul,
      Matrix.add_apply, vecMulVec_apply, v, complexFrequency]
    ring
  rw [eq]
  simp only [regularizedComplexGaugeProjection, mul_smul_comm, smul_mul_assoc]
  rw [smul_comm (gaugeProjectionInfrared ‖ξ‖ : ℂ) Complex.I]
  exact smul_eq_zero_of_right _ (regularizedComplexGaugeProjection_kills ξ v)

end Burnett.P01
