import Burnett.Analysis.GaugeProjection.GaugeProjectionFourier
import Burnett.Analysis.GaugeProjection.GaugeProjectionSchwartzAction

set_option autoImplicit false
set_option maxHeartbeats 3600000

noncomputable section

namespace Burnett.P01

open Burnett.A02.FrequencySplit (E tau radianFourier radianFourier_scaled)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open scoped BigOperators FourierTransform

/-- Complex Schwartz fields with two fixed coordinate indices. -/
abbrev ProjectionSchwartzMatrix := Fin 4 → Fin 4 → SchwartzMap E ℂ

/-- The coordinate derivative of each Schwartz matrix entry. -/
def projectionMatrixDerivative (b : Fin 4) (w : ProjectionSchwartzMatrix) : ProjectionSchwartzMatrix :=
  fun i j => coordinateDerivative b (w i j)

/-- The full matrix multiplier on Schwartz inputs using its existing scalar
Schwartz components. -/
def projectionFullSchwartz (w : ProjectionSchwartzMatrix) : ProjectionSchwartzMatrix :=
  fun i j => ∑ a, ∑ b, gaugeProjectionSchwartzComponent i j a b (w a b)

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def radianEval (ξ : E) : SchwartzMap E ℂ →+ ℂ where
  toFun f := radianFourier f ξ
  map_zero' := by
    have h := radianFourier_scaled (0 : SchwartzMap E ℂ) (tau⁻¹ • ξ)
    rw [smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul] at h
    rw [h]
    change SchwartzMap.fourierTransformCLM ℂ 0 _ = _
    rw [map_zero, SchwartzMap.zero_apply]
  map_add' f g := by
    have h (u : SchwartzMap E ℂ) := radianFourier_scaled u (tau⁻¹ • ξ)
    simp only [smul_smul, mul_inv_cancel₀ tau_pos.ne', one_smul] at h
    simp only [h]
    change SchwartzMap.fourierTransformCLM ℂ (f + g) _ =
      SchwartzMap.fourierTransformCLM ℂ f _ + SchwartzMap.fourierTransformCLM ℂ g _
    rw [map_add, SchwartzMap.add_apply]

private theorem radianFourierSchwartz_injective :
    Function.Injective (fun f : SchwartzMap E ℂ => radianFourier f) := by
  intro f g h
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ν
  change 𝓕 (f : E → ℂ) ν = 𝓕 (g : E → ℂ) ν
  rw [← radianFourier_scaled, ← radianFourier_scaled]
  exact congrFun h _

/-- Fourier transform of the actual four-index projection. -/
theorem projectionFullSchwartz_radianFourier
    (w : ProjectionSchwartzMatrix) (i j : Fin 4) (ξ : E) :
    radianFourier (projectionFullSchwartz w i j) ξ =
      regularizedComplexGaugeProjection ξ (fun a b => radianFourier (w a b) ξ) i j := by
  rw [regularizedComplexGaugeProjection_apply]
  change radianEval ξ (∑ a, ∑ b, gaugeProjectionSchwartzComponent i j a b (w a b)) = _
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  exact gaugeProjectionSchwartzComponent_radianFourier i j a b (w a b) ξ

theorem projectionFullSchwartz_add (f g : ProjectionSchwartzMatrix) :
    projectionFullSchwartz (f + g) = projectionFullSchwartz f + projectionFullSchwartz g := by
  funext i j
  simp only [projectionFullSchwartz, Pi.add_apply, map_add, Finset.sum_add_distrib]

/-- The original projection removes the whole symmetrized gradient on
Schwartz covectors. -/
theorem projectionFullSchwartz_symmetrizedGradient_eq_zero
    (V : Fin 4 → SchwartzMap E ℂ) :
    projectionFullSchwartz (fun a b => coordinateDerivative a (V b) + coordinateDerivative b (V a)) =
      0 := by
  funext i j
  apply radianFourierSchwartz_injective
  funext ξ
  change radianFourier (projectionFullSchwartz
    (fun a b => coordinateDerivative a (V b) + coordinateDerivative b (V a)) i j) ξ =
      radianFourier (0 : SchwartzMap E ℂ) ξ
  rw [projectionFullSchwartz_radianFourier,
    regularizedComplexGaugeProjection_symmetrizedGradient]
  exact (radianEval ξ).map_zero.symm

/-- The projection commutes with the actual coordinate derivative. -/
theorem projectionFullSchwartz_coordinateDerivative (a : Fin 4) (w : ProjectionSchwartzMatrix) :
    projectionFullSchwartz (projectionMatrixDerivative a w) =
      projectionMatrixDerivative a (projectionFullSchwartz w) := by
  funext i j
  apply radianFourierSchwartz_injective
  funext ξ
  change radianFourier (projectionFullSchwartz (projectionMatrixDerivative a w) i j) ξ =
    radianFourier (coordinateDerivative a (projectionFullSchwartz w i j)) ξ
  rw [radianFourier_coordinateDerivative, projectionFullSchwartz_radianFourier,
    projectionFullSchwartz_radianFourier]
  simp only [regularizedComplexGaugeProjection_apply, projectionMatrixDerivative,
    radianFourier_coordinateDerivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  ring

end Burnett.P01
