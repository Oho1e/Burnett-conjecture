import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCyclicCubicExpansion
import Burnett.Analysis.CubicEnergy.CompleteEnergy.FixedInfraredStructure

set_option autoImplicit false
set_option maxRecDepth 6400
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.C02

open MeasureTheory Burnett.RicciSymbol Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz_radianFourier
  gaugeProjectionInfrared_zero regularizedComplexGaugeProjection)
open Burnett.V08 (originalGaugeSpectrum signedCyclicPhase)

theorem wardActualThinSpectrum_zero_of_smallFrequency (m : Tensor2)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (ξ : E) (hξ : ‖ξ‖ ≤ 1) :
    wardActualThinSpectrum m wi wo hm hη i o z ξ = 0 := by
  funext a b
  rw [wardActualThinSpectrum_eq_sum m wi wo hm hη i o z ξ (a,b)]
  apply Finset.sum_eq_zero
  intro j _
  rw [projectionFullSchwartz_radianFourier]
  simp only [regularizedComplexGaugeProjection, gaugeProjectionInfrared_zero hξ,
    Complex.ofReal_zero, zero_smul, Matrix.zero_apply, mul_zero]

theorem wardOriginalGaugeSpectrum_zero_of_smallFrequency
    (z : ProjectionSchwartzMatrix) (ξ : E) (hξ : ‖ξ‖ ≤ 1) :
    originalGaugeSpectrum z ξ = 0 := by
  funext a b
  change radianFourier (Burnett.C03.projectedGaugeComplement z a b) ξ = 0
  rw [Burnett.C03.projectedGaugeComplement_radianFourier, gaugeProjectionInfrared_zero hξ,
    Complex.ofReal_zero, zero_mul]

/-- The homogeneous and infrared-modified tests give exactly the same
cyclic weight whenever all three original spectra vanish on the low ball. -/
theorem wardCyclicCubicWeight_congr_of_high_frequency (G : Mat) (hG : Matrix.det G ≠ 0)
    (a b : E → ℝ) (hab : ∀ ξ, 1 < ‖ξ‖ → a ξ = b ξ) (F H J : E → ComplexTensor2)
    (hF : ∀ ξ, ‖ξ‖ ≤ 1 → F ξ = 0) (hH : ∀ ξ, ‖ξ‖ ≤ 1 → H ξ = 0)
    (hJ : ∀ ξ, ‖ξ‖ ≤ 1 → J ξ = 0) (x : Joint) :
    wardCyclicCubicWeight G a F H J x = wardCyclicCubicWeight G b F H J x := by
  let p := x.1
  let q := x.2
  let r := -(p+q)
  let P : Cov := fun d => p d
  let Q : Cov := fun d => q d
  let R : Cov := fun d => r d
  let W := complexPrincipalVertex G P (F p) Q (H q) R (J r)
  change (-Complex.I / 3) * ((a p + a q + a r : ℝ) : ℂ) * W =
    (-Complex.I / 3) * ((b p + b q + b r : ℝ) : ℂ) * W
  by_cases hp : 1 < ‖p‖
  · by_cases hq : 1 < ‖q‖
    · by_cases hr : 1 < ‖r‖
      · rw [hab p hp,hab q hq,hab r hr]
      · have hW : W = 0 := by
          have h := complexPrincipalVertex_smul_third_amplitude G hG P (F p) Q (H q) R (J r) 0
          simpa only [W, zero_smul, zero_mul, hJ r (le_of_not_gt hr)] using h
        rw [hW,mul_zero,mul_zero]
    · have hW : W = 0 := by
        have h := complexPrincipalVertex_smul_second_amplitude G hG P (F p) Q (H q) R (J r) 0
        simpa only [W, zero_smul, zero_mul, hH q (le_of_not_gt hq)] using h
      rw [hW,mul_zero,mul_zero]
  · have hW : W = 0 := by
      have h := complexPrincipalVertex_smul_first_amplitude G hG P (F p) Q (H q) R (J r) 0
      simpa only [W, zero_smul, zero_mul, hF p (le_of_not_gt hp)] using h
    rw [hW,mul_zero,mul_zero]

/-- The paper's homogeneous test can be used for the actual frozen
thin-plus-gauge input after C02's fixed infrared replacement. -/
theorem wardActualCyclicCubicForm_fixedInfrared_test (G : Mat) (hG : Matrix.det G ≠ 0)
    (a : E → ℝ) (cut add : SchwartzMap E ℂ)
    (hCut : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile cut ξ = 0)
    (hAdd : ∀ ξ, 1 < ‖ξ‖ → fixedRadianProfile add ξ = 0)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    let Q := originalGaugeSpectrum z
    wardCyclicCubicForm G (fixedInfraredSymbol cut add a) (H+Q) (H+Q) (H+Q) =
      wardCyclicCubicForm G a (H+Q) (H+Q) (H+Q) := by
  intro H Q
  have hz (ξ : E) (hξ : ‖ξ‖ ≤ 1) : (H+Q) ξ = 0 := by
    change H ξ + Q ξ = 0
    have hv : H ξ = 0 := wardActualThinSpectrum_zero_of_smallFrequency
      (inverseMatrix G) wi wo hm hη i o z ξ hξ
    have hq : Q ξ = 0 := wardOriginalGaugeSpectrum_zero_of_smallFrequency z ξ hξ
    rw [hv,hq,zero_add]
  unfold wardCyclicCubicForm
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (wardCyclicCubicWeight_congr_of_high_frequency G hG _
    a (fun ξ hξ => fixedInfraredSymbol_outside cut add a ξ (hCut ξ hξ) (hAdd ξ hξ))
    (H+Q) (H+Q) (H+Q) hz hz hz)

end Burnett.C02
