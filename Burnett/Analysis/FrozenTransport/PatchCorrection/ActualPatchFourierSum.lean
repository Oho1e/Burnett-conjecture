import Burnett.Analysis.FrozenTransport.PatchCorrection.CommonFarGaugePatchBudget
import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalPatchSourceIdentity
import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarSelectedGuard

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option maxRecDepth 4900

noncomputable section

namespace Burnett.V11

open Set Metric Matrix MeasureTheory Burnett.P01 Burnett.C02 Burnett.V08 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open Burnett.V10.OriginalGaugeCompatibility
open Burnett.A02.FrequencySplit (E Joint tau)
open Burnett.Analysis.TransportWardSymbol (inverseMatrix)
open Burnett.C01 (patchCenter)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped ContDiff ComplexConjugate BigOperators Matrix Matrix.Norms.Elementwise

/-- On the already chosen patch family, recover the literal two original
Fourier integrals, with their individual absolute values and common sum. -/
theorem originalCorrectionFourierSum_of_sharedBudget
    (g₀ : E → Tensor2) (K : Set E) (symm : ∀ x ∈ K, (g₀ x)ᵀ = g₀ x)
    (a : Joint → ℝ) (ha : ∀ x ∈ K, ContDiffOn ℝ ∞ (fun ξ => a (x, ξ)) ({0}ᶜ : Set E))
    (odd : ∀ x ∈ K, ∀ ξ : E, a (x, -ξ) = -a (x, ξ))
    (hom : ∀ x ∈ K, ∀ t : ℝ, 0 < t → ∀ ξ : E, a (x, t • ξ) = t * a (x, ξ))
    (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ) (cut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (bounded : ∀ t : ℝ, |ϑ t| ≤ 1)
    (κ : ℝ) (hκ : 0 < κ) (hsmall : κ < 1 / 16) (δ b i o : ℝ)
    (wide : ∀ x ∈ K, WideScreenFrequencySmooth i o (inverseMatrix (g₀ x)))
    {η : ℝ} (hη : 0 < η) (inn out : ℝ) (S : E → GaugeScreen)
    (same : ∀ x (hx : x ∈ K), S x = (thinScreenAngular (inverseMatrix (g₀ x)) i o (wide x hx) hη inn out).matrix)
    (phase : ∀ x (hx : x ∈ K), ActualFarPhaseIdentities (g₀ x) (fun ξ => a (x, ξ))
      ϑ κ δ b i o (wide x hx) hη inn out)
    (M : ℝ) (hM : 0 ≤ M)
    (jet : ∀ x (hx : x ∈ K), ∀ k J I, GaugeProfileBound 0 M
      (actualFarAngularProfile (g₀ x) (fun ξ => a (x, ξ)) ϑ κ δ b i o (wide x hx) hη inn out k J I))
    (ℓ : ℝ) (s : Finset LatticeIndex) (centers : ∀ j ∈ s, patchCenter ℓ j ∈ K)
    (Z : LatticeIndex → ProjectionSchwartzMatrix) (realZ : ∀ j ∈ s, ∀ r t y, conj (Z j r t y) = Z j r t y)
    (budget : ℝ) :
    let x := patchCenter ℓ
    let G := originalMetricGaugeEnergy ϑ κ g₀ a S
    let F := originalMetricFarEnergy g₀ a ϑ κ δ b i o K wide hη inn out
    let NWG (j : LatticeIndex) := originalGaugePhysicalNumerator ϑ κ (g₀ (x j)) (fun ξ => a (x j, ξ)) (S (x j)) (Z j)
    let NWF (j : LatticeIndex) : Joint → ℂ := by
      classical
      exact if hx : x j ∈ K then originalFarPatchFourierWeight (g₀ (x j)) (fun ξ => a (x j, ξ))
        ϑ κ δ i o (wide (x j) hx) hη inn out (Z j) else 0
    (∑ j ∈ s, (‖G (x j) (Z j)‖ + ‖F (x j) (Z j)‖)) ≤ budget →
    (∀ j ∈ s, Integrable (NWG j) ∧ Integrable (NWF j)) ∧
    (∑ j ∈ s, (‖(tau ^ 8)⁻¹ • ∫ y, NWG j y‖ + ‖(tau ^ 8)⁻¹ • ∫ y, NWF j y‖)) ≤ budget := by
  classical
  intro x G F NWG NWF estimate
  have readback (j : LatticeIndex) (hj : j ∈ s) : Integrable (NWG j) ∧ Integrable (NWF j) ∧
      ((tau ^ 8)⁻¹ • (∫ y, NWG j y) = G (x j) (Z j)) ∧
      (tau ^ 8)⁻¹ • (∫ y, NWF j y) = F (x j) (Z j) := by
    have hx : x j ∈ K := centers j hj
    obtain ⟨gInt, gEq, _⟩ := originalPatchSource_fullIdentity ϑ hϑ cut bounded κ hκ hsmall (g₀ (x j))
      (symm _ hx) (fun ξ => a (x j, ξ)) (ha _ hx) (odd _ hx) (hom _ hx) i o (wide _ hx) hη inn out
      (Z j) (realZ j hj)
    have zeroJet (k J I : TensorSlot) (y : Joint × E) (hy : y ∈ gaugeAngularWindow) :
        ‖actualFarAngularProfile (g₀ (x j)) (fun ξ => a (x j, ξ)) ϑ κ δ b i o (wide _ hx) hη inn out k J I y‖ ≤ M := by
      obtain ⟨_, _, _, _, bound⟩ := jet _ hx k J I
      simpa only [norm_iteratedFDeriv_zero] using bound 0 le_rfl y hy
    have fWeight : NWF j = originalFarPatchFourierWeight (g₀ (x j)) (fun ξ => a (x j, ξ))
        ϑ κ δ i o (wide _ hx) hη inn out (Z j) := dif_pos hx
    have fEnergy : F (x j) (Z j) = actualFarPatchEnergy (g₀ (x j)) (fun ξ => a (x j, ξ))
        ϑ κ δ b i o (wide _ hx) hη inn out (Z j) := dif_pos hx
    obtain ⟨fInt, fEq⟩ := originalFarPatch_fourierEnergy_of_phase (g₀ (x j)) (fun ξ => a (x j, ξ))
      (ha _ hx) ϑ hϑ cut κ hκ hsmall δ b i o (wide _ hx) hη inn out (phase _ hx) M hM zeroJet (Z j)
    rw [fWeight, fEnergy]
    refine ⟨?_, fInt, ?_, fEq⟩
    · simpa only [NWG, same _ hx] using gInt
    · simpa only [NWG, G, originalMetricGaugeEnergy, same _ hx] using gEq
  refine ⟨fun j hj => ⟨(readback j hj).1, (readback j hj).2.1⟩, ?_⟩
  calc
    _ = ∑ j ∈ s, (‖G (x j) (Z j)‖ + ‖F (x j) (Z j)‖) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [(readback j hj).2.2.1, (readback j hj).2.2.2]
    _ ≤ _ := estimate

end Burnett.V11
