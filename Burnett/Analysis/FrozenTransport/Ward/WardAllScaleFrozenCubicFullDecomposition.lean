import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePhysicalPhaseRecombination
import Burnett.Analysis.FrozenTransport.Ward.WardAllScalePurePhysicalDecomposition

set_option autoImplicit false
set_option maxRecDepth 7400
set_option maxHeartbeats 8500000

noncomputable section

namespace Burnett.C02

open Matrix MeasureTheory Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V08 (originalGaugeSpectrum)
open scoped Matrix ComplexConjugate

/-- All four terms of the original frozen assembly on one actual patch.
The far and gauge integrals keep their exact signed weights, and the
phase remainder is the one controlled by the common C02 patch bound. -/
theorem wardActualFrozenCubic_fullDecomposition (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G)) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) :
    let m := inverseMatrix G
    let w := metricDensity G
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let Q := originalGaugeSpectrum z
    let W := wardCyclicCubicWeight G a H H H
    let F (y : Joint) := (wardPurePhysicalFirstFarWeight ϑ κ δ y : ℂ) * W y
    let N (y : Joint) := (wardPurePhysicalNearWeight ϑ κ δ y : ℂ) * W y
    let K := wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z
    let I (A : Joint → ℂ) := ((tau^8)⁻¹ : ℝ) • (∫ x, A x)
    Integrable W → Integrable F → Integrable K →
    (∀ s : Fin 7, Integrable (wardActualTensorWeight m (wardPhysicalPhaseSlots s)
      (wardPhysicalPhaseTensorSymbol ϑ κ m w a s) wi wo hm hη i o z)) →
    Integrable N ∧
    wardCyclicCubicForm G a (H+Q) (H+Q) (H+Q) =
      I N + 3 * I F + 3 * I K + wardPhysicalPhaseRemainder ϑ κ m w a wi wo hm hη i o z := by
  intro m w H Q W F N K I hW hF hK hSeven
  have hPure := wardPurePhysicalCubicForm_eq_near_add_far G a H ϑ κ δ hW hF
  have h := wardCyclicActualFrozenGaugeDecomposition_recombined G hG hg f a ϑ κ wi wo hm hη i o ε hi hio hSmall
    hWindow z hz hReal hW hK hSeven
  refine ⟨hPure.1, h.trans ?_⟩
  rw [hPure.2]

end Burnett.C02
