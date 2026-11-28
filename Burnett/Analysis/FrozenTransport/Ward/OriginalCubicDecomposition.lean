import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleCompleteActualPatch
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleFarWardNumerator
import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarFrequencyEnergy
import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalPatchSourceIdentity
set_option autoImplicit false
set_option maxHeartbeats 9000000
set_option maxRecDepth 7400

noncomputable section

namespace Burnett.V03

open Matrix MeasureTheory Metric Set Burnett.A02.FrequencySplit Burnett.C02 Burnett.RicciSymbol Burnett.V06
open Burnett.Analysis.TransportWardSymbol Burnett.V10.OriginalGaugeCompatibility
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.P01 (ProjectionSchwartzMatrix)
open Burnett.V11 (originalGaugePhysicalNumerator)
open scoped BigOperators ComplexConjugate ContDiff Matrix

/-- The Ward correction and the V11 correction use exactly the same
ordered gauge numerator and the same original projections. -/
theorem wardOrderedGaugeCorrectionNumerator_eq_originalGaugePhysicalNumerator
    (G : Mat) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) :
    wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z =
      originalGaugePhysicalNumerator ϑ κ G a
        (thinScreenAngular (inverseMatrix G) wi wo hm hη i o).matrix z := by
  rfl

/-- The Ward first far slot is exactly the integrand bounded by the
original V11 physical far correction. -/
theorem wardPurePhysicalFarWeight_eq_originalFarPatchFourierWeight
    (G : Mat) (hG : Matrix.det G ≠ 0) (a : E → ℝ) (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o : ℝ) (z : ProjectionSchwartzMatrix) (hz : ∀ a b x, conj (z a b x) = z a b x) :
    let H := wardActualThinSpectrum (inverseMatrix G) wi wo hm hη i o z
    (fun x => (wardPurePhysicalFirstFarWeight ϑ κ δ x : ℂ) * wardCyclicCubicWeight G a H H H x) =
      originalFarPatchFourierWeight G a ϑ κ δ wi wo hm hη i o z := by
  intro H
  funext x
  unfold wardPurePhysicalFirstFarWeight
  rw [wardActualFarWeight_eq_original_numerator G hG a ϑ κ δ wi wo hm hη i o z hz]
  rfl

/-- The frozen energy of the original raw patch equals its thin replacement
error and the same four terms used by the C02 and V11 tail estimates. -/
theorem originalRawFrozenCubic_eq_thinReplacement_add_Ward
    (G : Mat) (hG : IsUnit G) (hg : IsSymmetricTensor G)
    (f : TensorFrame.LorentzFrame (inverseMatrix G))
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (D : ℝ) (hD : 0 ≤ D) (hJets : ∀ n : ℕ, n ≤ 16 → ∀ ξ ∈ sphere (0 : E) 1,
      ‖iteratedFDeriv ℝ n a ξ‖ ≤ D)
    (ϑ : ℝ → ℝ) (κ δ wi wo : ℝ)
    (hm : WideScreenFrequencySmooth wi wo (inverseMatrix G)) {η : ℝ} (hη : 0 < η)
    (i o ε : ℝ) (hi : 0 ≤ i) (hio : i < o) (hSmall : o * η ≤ ε)
    (hWindow : ∀ e : Covector, e ⬝ᵥ e = 1 → |symbolNorm (inverseMatrix G) e| < ε →
      screenSecondDirection (inverseMatrix G) e ≠ 0 ∧
      IsUnit (screenMetricExtension (inverseMatrix G) (screenDirectionProjection (inverseMatrix G) e)).det)
    (z : ProjectionSchwartzMatrix) (hz : ∀ a b, z a b = z b a)
    (hReal : ∀ a b x, conj (z a b x) = z a b x) :
    let m := inverseMatrix G
    let β := fixedInfraredSymbol wardFixedTestCutoff 0 a
    let raw : RealEnergyField OrderedPair := ⟨fun k => z k.1 k.2, fun k => hReal k.1 k.2⟩
    let thin := originalCubicThinScreen m wi wo hm hη i o z hReal + originalCubicGauge z hReal
    let E₀ := completeCubicEnergy (frozenActionCubicLinear G) (frozenActionCubicQuadratic G) β
    let H := wardActualThinSpectrum m wi wo hm hη i o z
    let near := ((tau^8)⁻¹ : ℝ) • ∫ x, (wardPurePhysicalNearWeight ϑ κ δ x : ℂ) *
      wardCyclicCubicWeight G a H H H x
    let far := originalFarPatchFourierWeight G a ϑ κ δ wi wo hm hη i o z
    let gauge := originalGaugePhysicalNumerator ϑ κ G a (thinScreenAngular m wi wo hm hη i o).matrix z
    let phase := wardPhysicalPhaseRemainder ϑ κ m (metricDensity G) a wi wo hm hη i o z
    let I (A : Joint → ℂ) := ((tau^8)⁻¹ : ℝ) • (∫ x, A x)
    Integrable far → Integrable gauge →
    (∀ s : Fin 7, Integrable (wardActualTensorWeight m (wardPhysicalPhaseSlots s)
      (wardPhysicalPhaseTensorSymbol ϑ κ m (metricDensity G) a s) wi wo hm hη i o z)) →
    E₀ raw = near.re + (E₀ raw - E₀ thin) + phase.re + (3 * (I far).re + 3 * (I gauge).re) := by
  intro m β raw thin E₀ H near far gauge phase I hFar hGauge hSeven
  have hDet : Matrix.det G ≠ 0 := isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det G).mp hG)
  have hF := wardPurePhysicalFarWeight_eq_originalFarPatchFourierWeight G hDet a ϑ κ δ wi wo hm hη i o z hReal
  have hK := wardOrderedGaugeCorrectionNumerator_eq_originalGaugePhysicalNumerator G a ϑ κ wi wo hm hη i o z
  have hFar' : Integrable (fun x => (wardPurePhysicalFirstFarWeight ϑ κ δ x : ℂ) *
      wardCyclicCubicWeight G a H H H x) := by rw [hF]; exact hFar
  have hGauge' : Integrable (wardOrderedGaugeCorrectionNumerator ϑ κ G a wi wo hm hη i o z) := by rw [hK]; exact hGauge
  obtain ⟨_, hsplit⟩ := wardCompleteActualFrozenPatch_eq_original_four_terms G hG hg f a ha hOdd hHom
    D hD hJets ϑ κ δ wi wo hm hη i o ε hi hio hSmall hWindow z hz hReal hFar' hGauge' hSeven
  have hIdentity : E₀ thin = (near + 3 * I far + 3 * I gauge + phase).re := by
    dsimp only at hsplit
    rw [hF, hK] at hsplit
    exact hsplit
  rw [hIdentity]
  simp only [Complex.add_re, Complex.mul_re]
  norm_num
  all_goals ring

end Burnett.V03
