import Burnett.Analysis.FrozenTransport.UniformOriginalThinCubicFamily
import Burnett.Analysis.TransportPatches.ActualThinScreenCombination

set_option autoImplicit false
set_option maxRecDepth 5300
set_option maxHeartbeats 9100000
noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Matrix Burnett.Fourier Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E tau radianFourier radianFourier_scaled euclideanFieldGradientL3)
open Burnett.A07 (coordinateDerivative radianFourier_coordinateDerivative)
open Burnett.P01 (ProjectionSchwartzMatrix principalGaugeProjectionMatrix gaugeProjectionInfrared)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.ProjectiveNullCaps (quadratic_neg)
open scoped BigOperators ComplexConjugate ContDiff ENNReal FourierTransform Matrix

open private angularOutput_mulScalar from Burnett.Analysis.TransportPatches.ActualThinScreenCombination

private theorem normalizedFrozenPhase_even (m : Tensor2) (ξ : E) :
    normalizedFrozenPhase m (-ξ) = normalizedFrozenPhase m ξ := by
  simp only [normalizedFrozenPhase, quadratic_neg, norm_neg]

private def thinPhaseAngular (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) : RealOrderedAngularMatrix where
  matrix ξ := normalizedFrozenPhase m ξ • (thinScreenAngular m wi wo hm hη i o).matrix ξ
  smooth k j := (normalizedFrozenPhase_contDiffOn m).mul ((thinScreenAngular m wi wo hm hη i o).smooth k j)
  degree t ht ξ := by rw [normalizedFrozenPhase_degreeZero m t ht ξ,
    (thinScreenAngular m wi wo hm hη i o).degree t ht ξ]

private theorem thinPhaseAngular_even (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (ξ : E) :
    (thinPhaseAngular m wi wo hm hη i o).matrix (-ξ) = (thinPhaseAngular m wi wo hm hη i o).matrix ξ := by
  simp only [thinPhaseAngular, normalizedFrozenPhase_even, thinScreenAngular_even]

private def phaseMultiplierAfterThinScreen (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ) :
    ClassicalMatrixMultiplier OrderedPair :=
  (thinPhaseAngular m wi wo hm hη i o).afterOriginalProjection

private theorem phaseMultiplierAfterThinScreen_output (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : OrderedPair → ComplexL2 E) (k : OrderedPair) :
    (phaseMultiplierAfterThinScreen m wi wo hm hη i o).output z k =
      fourierMultiplier (frozenPhaseScalar m) ((actualThinScreenMultiplier m wi wo hm hη i o).output z k) := by
  let S := thinScreenAngular m wi wo hm hη i o
  let T := thinPhaseAngular m wi wo hm hη i o
  change T.afterOriginalProjection.output z k =
    fourierMultiplier (frozenPhaseScalar m) (S.afterOriginalProjection.output z k)
  rw [T.afterOriginalProjection_output, S.afterOriginalProjection_output]
  apply angularOutput_mulScalar
  intro k j ξ
  rw [frozenPhaseScalar_apply]
  simp only [T, S, thinPhaseAngular, RealOrderedAngularMatrix.complex, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_mul]

private theorem phaseMultiplierAfterThinScreen_entry (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (k j : OrderedPair) (ξ : E) :
    (phaseMultiplierAfterThinScreen m wi wo hm hη i o).full k j ξ =
      (normalizedFrozenPhase m ξ : ℂ) * (actualThinScreenMultiplier m wi wo hm hη i o).full k j ξ := by
  let S := thinScreenAngular m wi wo hm hη i o
  let T := thinPhaseAngular m wi wo hm hη i o
  change T.afterOriginalProjection.full k j ξ =
    (normalizedFrozenPhase m ξ : ℂ) * S.afterOriginalProjection.full k j ξ
  rw [T.afterOriginalProjection_full, S.afterOriginalProjection_full]
  change (gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) * (T.complex ξ * principalGaugeProjectionMatrix ξ) k j =
    (normalizedFrozenPhase m ξ : ℂ) *
      ((gaugeProjectionInfrared ‖tau • ξ‖ : ℂ) * (S.complex ξ * principalGaugeProjectionMatrix ξ) k j)
  simp only [S, T, thinPhaseAngular, Matrix.mul_apply, RealOrderedAngularMatrix.complex, Matrix.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, mul_assoc, ← Finset.mul_sum]
  ring

/-- The actual phase-dressed thin-screen field in Schwartz space. It uses
exactly the original infrared factor and includes the exterior support. -/
def actualWardPhaseSchwartz (m : Tensor2) (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m)
    {η : ℝ} (hη : 0 < η) (i o : ℝ) (z : ProjectionSchwartzMatrix) : OrderedPair → SchwartzMap E ℂ :=
  (phaseMultiplierAfterThinScreen m wi wo hm hη i o).schwartzOutput
    ((thinPhaseAngular m wi wo hm hη i o).afterOriginalProjection_full_hasTemperateGrowth
      (thinPhaseAngular_even m wi wo hm hη i o)) z

theorem actualWardPhaseSchwartz_coordinateDerivative (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (a : Index) (k : OrderedPair) :
    (coordinateDerivative a (actualWardPhaseSchwartz m wi wo hm hη i o z k)).toLp 2 volume =
      fourierMultiplier (frozenPhaseScalar m)
        (multiplierCoordinateDerivative (actualThinScreenMultiplier m wi wo hm hη i o) z a k) := by
  rw [actualWardPhaseSchwartz, ClassicalMatrixMultiplier.schwartzOutput_coordinateDerivative]
  exact phaseMultiplierAfterThinScreen_output m wi wo hm hη i o
    (fun j => (coordinateDerivative a (z j.1 j.2)).toLp 2 volume) k

theorem actualWardPhaseSchwartz_gradientL3 (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) :
    euclideanFieldGradientL3 (actualWardPhaseSchwartz m wi wo hm hη i o z) =
      (eLpNorm (orderedGradientValue (fun a : Index × OrderedPair =>
        fourierMultiplier (frozenPhaseScalar m)
          (multiplierCoordinateDerivative (actualThinScreenMultiplier m wi wo hm hη i o) z a.1 a.2))) 3 volume).toReal :=
  euclideanFieldGradientL3_of_orderedDerivative _ _
    (fun a => actualWardPhaseSchwartz_coordinateDerivative m wi wo hm hη i o z a.1 a.2)

private theorem matrixSchwartzOutput_fourier {J : Type*} (T : ClassicalMatrixMultiplier J)
    (hT : ∀ k i, Function.HasTemperateGrowth (T.full k i : E → ℂ))
    (z : ProjectionSchwartzMatrix) (k : J) (ξ : E) :
    𝓕 (T.schwartzOutput hT z k : E → ℂ) ξ =
      ∑ j : OrderedPair, T.full k j ξ * 𝓕 (z j.1 j.2 : E → ℂ) ξ := by
  let e : SchwartzMap E ℂ →+ ℂ :=
    { toFun := fun v => (SchwartzMap.fourierTransformCLM ℂ v) ξ
      map_zero' := by simp only [map_zero, SchwartzMap.zero_apply]
      map_add' := fun _ _ => by simp only [map_add, SchwartzMap.add_apply] }
  change e (∑ j : OrderedPair, transportSchwartzMultiplier (T.full k j) (hT k j) (z j.1 j.2)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact transportSchwartzMultiplier_fourier _ _ _ _

/-- Pointwise radian-frequency factorization on the actual phase-bearing
field. The identity is available directly in the original triad integral. -/
theorem actualWardPhaseSchwartz_radianFourier (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (k : OrderedPair) (ξ : E) :
    radianFourier (actualWardPhaseSchwartz m wi wo hm hη i o z k) ξ =
      (normalizedFrozenPhase m ξ : ℂ) * radianFourier (actualThinSchwartzField m wi wo hm hη i o z k) ξ := by
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have hPos : 0 < tau⁻¹ := inv_pos.mpr hτ
  have scale : tau • (tau⁻¹ • ξ) = ξ := by rw [smul_smul, mul_inv_cancel₀ hτ.ne', one_smul]
  rw [← scale, radianFourier_scaled, radianFourier_scaled]
  rw [actualWardPhaseSchwartz, actualThinSchwartzField,
    matrixSchwartzOutput_fourier, matrixSchwartzOutput_fourier, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [phaseMultiplierAfterThinScreen_entry, scale, normalizedFrozenPhase_degreeZero _ _ hPos]
  ring

theorem actualWardPhaseSchwartz_coordinateDerivative_radianFourier (m : Tensor2) (wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η) (i o : ℝ)
    (z : ProjectionSchwartzMatrix) (a : Index) (k : OrderedPair) (ξ : E) :
    radianFourier (coordinateDerivative a (actualWardPhaseSchwartz m wi wo hm hη i o z k)) ξ =
      (normalizedFrozenPhase m ξ : ℂ) *
        radianFourier (coordinateDerivative a (actualThinSchwartzField m wi wo hm hη i o z k)) ξ := by
  rw [radianFourier_coordinateDerivative, radianFourier_coordinateDerivative, actualWardPhaseSchwartz_radianFourier]
  ring

end Burnett.C02
