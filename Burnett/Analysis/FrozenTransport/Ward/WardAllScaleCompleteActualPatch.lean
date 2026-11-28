import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualCyclicFixedInput
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFrozenCubicFullDecomposition

set_option autoImplicit false
set_option maxRecDepth 7800
set_option maxHeartbeats 9500000

noncomputable section

namespace Burnett.C02

open Matrix MeasureTheory Burnett.RicciSymbol Burnett.V06 Burnett.A02.FrequencySplit
open Burnett.Analysis.TransportWardSymbol
open Burnett.P01 (ProjectionSchwartzMatrix)
open scoped ComplexConjugate Matrix ContDiff

/-- The actual C02 replacement energy on the original patch is the real
part of the exact near, far, gauge, and physical-phase assembly. -/
theorem wardCompleteActualFrozenPatch_eq_original_four_terms
    (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (D : ℝ) (hD : 0 ≤ D) (hJets : ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ Metric.sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n a ξ‖ ≤ D)
    (ϑ : ℝ → ℝ) (κ δ : ℝ)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) :
    let m := inverseMatrix G
    let b := fixedInfraredSymbol wardFixedTestCutoff 0 a
    let w := metricDensity G
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let u := originalCubicThinScreen m wi wo hm hη i o z hReal
    let g := originalCubicGauge z hReal
    let W := wardCyclicCubicWeight G a H H H
    let F (y : Joint) := (wardPurePhysicalFirstFarWeight ϑ κ δ y : ℂ) * W y
    let N (y : Joint) := (wardPurePhysicalNearWeight ϑ κ δ y : ℂ) * W y
    let K := wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z
    let I (A : Joint → ℂ) := ((tau^8)⁻¹ : ℝ) • (∫ x, A x)
    Integrable F → Integrable K →
    (∀ s : Fin 7, Integrable (wardActualTensorWeight m (wardPhysicalPhaseSlots s)
      (wardPhysicalPhaseTensorSymbol ϑ κ m w a s) wi wo hm hη i o z)) →
    Integrable N ∧
    completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) b (u+g) =
      (I N + 3 * I F + 3 * I K + wardPhysicalPhaseRemainder ϑ κ m w a wi wo hm hη i o z).re := by
  intro m b w H u g W F N K I hF hK hSeven
  have hDet : Matrix.det G ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hEnergy := wardActualThinGaugeFixedWindow_eq_fourier G hDet a ha hOdd hHom D hD hJets
    wi wo hm hη i o z hReal
  have hSplit := wardActualFrozenCubic_fullDecomposition G hG hg f a ϑ κ δ wi wo hm hη i o ε hi hio hSmall
    hWindow z hz hReal hEnergy.1 hF hK hSeven
  exact ⟨hSplit.1, hEnergy.2.symm.trans (congrArg Complex.re hSplit.2)⟩

end Burnett.C02
