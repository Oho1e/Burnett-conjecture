import Burnett.Analysis.FrozenTransport.Ward.ActualWardPhaseSchwartz
import Burnett.Analysis.FrozenTransport.Ward.WardThinScreenAnnihilation

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Matrix Burnett.Fourier Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.P01 (ComplexComponents ProjectionSchwartzMatrix projectionFullSchwartz
  projectionFullSchwartz_radianFourier regularizedComplexGaugeProjection_apply regularizedGaugeProjectionSymbol
  principalGaugeProjectionMatrix gaugeProjectionSymbol_scale gaugeProjectionInfrared)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped Matrix FourierTransform

open private matrixSchwartzOutput_fourier from Burnett.Analysis.FrozenTransport.Ward.ActualWardPhaseSchwartz

private theorem wardProjectedRadianSpectrum_eq_row (z : ProjectionSchwartzMatrix) (j : OrderedPair) (ξ : E) :
    radianFourier (projectionFullSchwartz z j.1 j.2) ξ = (gaugeProjectionInfrared ‖ξ‖ : ℂ) *
      ∑ i : OrderedPair, principalGaugeProjectionMatrix ξ j i * radianFourier (z i.1 i.2) ξ := by
  rw [projectionFullSchwartz_radianFourier, regularizedComplexGaugeProjection_apply]
  simp only [regularizedGaugeProjectionSymbol, Complex.ofReal_mul, principalGaugeProjectionMatrix,
    Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]

/-- The actual thin-screen Schwartz Fourier field, with both lower indices
retained in the original receiving coordinates. -/
def wardActualThinSpectrum (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (ξ : E) : ComplexComponents :=
  fun a b => radianFourier (actualThinSchwartzField m wi wo hm hη i o z (a,b)) ξ

/-- Exact column expansion of the actual thin screen composed with the
same full infrared-regularized projected Schwartz field. -/
theorem wardActualThinSpectrum_eq_sum (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) (ξ : E) (k : OrderedPair) :
    let S := thinScreenAngular m wi wo hm hη i o
    wardActualThinSpectrum m wi wo hm hη i o z ξ k.1 k.2 = ∑ j : OrderedPair,
      (S.matrix ξ k j : ℂ) * radianFourier (projectionFullSchwartz z j.1 j.2) ξ := by
  intro S
  let T := S.afterOriginalProjection
  let ζ := tau⁻¹ • ξ
  let χ := (gaugeProjectionInfrared ‖ξ‖ : ℂ)
  let R := principalGaugeProjectionMatrix ξ
  let u (b : OrderedPair) := radianFourier (z b.1 b.2) ξ
  let a (b : OrderedPair) := (S.matrix ξ k b : ℂ)
  have ht : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hζ : tau • ζ = ξ := by change tau • (tau⁻¹ • ξ) = ξ; rw [smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
  have hV : wardActualThinSpectrum m wi wo hm hη i o z ξ k.1 k.2 =
      ∑ b : OrderedPair, T.full k b ζ * u b := by
    change radianFourier (actualThinSchwartzField m wi wo hm hη i o z k) ξ = _
    rw [← hζ, radianFourier_scaled, actualThinSchwartzField, matrixSchwartzOutput_fourier]
    apply Finset.sum_congr rfl
    intro b _
    have hu : 𝓕 (z b.1 b.2 : E → ℂ) ζ = u b := by
      change _ = radianFourier (z b.1 b.2) ξ
      rw [← hζ, radianFourier_scaled]
    rw [hu]
    rfl
  have hS : S.complex ζ = S.complex ξ := by
    rw [← hζ]
    ext b c
    change (S.matrix ζ b c : ℂ) = (S.matrix (tau • ζ) b c : ℂ)
    rw [S.degree tau ht]
  have hR : principalGaugeProjectionMatrix ζ = R := by
    unfold R
    rw [← hζ]
    ext b c
    simp only [principalGaugeProjectionMatrix, gaugeProjectionSymbol_scale _ _ _ _ tau ht]
  have hFull (b : OrderedPair) : T.full k b ζ = χ * ∑ j : OrderedPair, a j * R j b := by
    change S.afterOriginalProjection.full k b ζ = _
    rw [S.afterOriginalProjection_full, hζ]
    change χ * (S.complex ζ * principalGaugeProjectionMatrix ζ) k b = _
    rw [hS, hR, Matrix.mul_apply]
    rfl
  rw [hV]
  simp only [hFull, wardProjectedRadianSpectrum_eq_row]
  change (∑ b, (χ * ∑ j, a j * R j b) * u b) = ∑ j, a j * (χ * ∑ b, R j b * u b)
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro b _
  ring

end Burnett.C02
