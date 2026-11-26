import Burnett.Analysis.FrozenTransport.PatchCorrection.CommonGaugePatchBudget
import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarPatchEnvelope

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4700

noncomputable section

namespace Burnett.V11

open Set MeasureTheory Burnett.P01 Burnett.V08 Burnett.C02 Burnett.C03 Burnett.RicciSymbol
open Burnett.V10.OriginalGaugeCompatibility
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix metricDensity)
open Burnett.Analysis.ProjectiveNullCaps (Vec)
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff ENNReal Matrix.Norms.Elementwise

private theorem profileOrder_mono {N₁ N₂ : ℕ} {M : ℝ} {F : Joint × E → ℂ}
    (hN : N₁ ≤ N₂) (hj : GaugeProfileBound N₂ M F) : GaugeProfileBound N₁ M F := by
  obtain ⟨W, openW, inc, smooth, jet⟩ := hj
  exact ⟨W, openW, inc, smooth, fun n hn p hp => jet n (hn.trans hN) p hp⟩

/-- A caller that already has the original C03 patch data can apply both
corrections to that very witness. Its other exponent bounds remain available
to the C02 and Ward consumers of the original patch. -/
theorem exists_actualCorrections_consume_sameProjectedPatch :
    ∃ (N : ℕ) (Corder Cweak : ℝ), 0 ≤ Corder ∧ 0 ≤ Cweak ∧
      ∀ (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ), ContDiffOn ℝ ∞ a {x : Vec | x ≠ 0} →
      (∀ x, a (-x) = -a x) → (∀ s : ℝ, 0 < s → ∀ x, a (s • x) = s * a x) →
      (∀ s : ℝ, 1 ≤ s → ϑ s = 0) → ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ δ b i o : ℝ,
      ∀ (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ),
      let m := inverseMatrix g
      let screen := (thinScreenAngular m i o hm hη inn out).matrix
      ∀ M : ℝ, 0 ≤ M → (∀ k J I, GaugeProfileBound N M
        (gaugeTriadAngularProfile ϑ κ m (metricDensity g) a (gaugeFrozenContraction m) screen k I J) ∧
        GaugeProfileBound N M (actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I)) →
      ∀ (d : Index → Index → SchwartzMap Vec ℝ) (A : ProjectedSourceCoefficients) (z : ProjectionSchwartzMatrix)
        (W : Set Vec) (B ℓ e : ℝ), 1 ≤ B → 0 < ℓ → 0 ≤ e → Corder * M ≤ B → 2 * Cweak * M ≤ B →
      (∀ r s, d r s = d s r) → (∀ r s x, A.entry r s x = ((m r s + d r s x : ℝ) : ℂ)) →
      GaugePatchCoefficientBounds B ℓ e d z W →
      (‖projectedSourceDivergenceL2 A (projectionFullSchwartz z)‖ ≤
        B * (volume W ^ ((1 : ℝ) / 2)).toReal * (1 + ℓ⁻¹ + (ℓ ^ 2)⁻¹ * e)) →
      ‖originalGaugePatchEnergy ϑ κ m (metricDensity g) a (gaugeFrozenContraction m) screen z‖ +
        ‖actualFarPatchEnergy g a ϑ κ δ b i o hm hη inn out z‖ ≤
          (16 ^ 3 : ℝ) * (6 * B ^ 5) * (volume W).toReal * Burnett.C04.correctionEnvelope ℓ e := by
  obtain ⟨NG, CoG, CwG, hCoG, hCwG, gauge⟩ := exists_originalGauge_patchEnvelope
  obtain ⟨NF, CoF, CwF, hCoF, hCwF, far⟩ := exists_actualFar_projectedPatch_envelope
  refine ⟨max NG NF, CoG + CoF, CwG + CwF, add_nonneg hCoG hCoF, add_nonneg hCwG hCwF, ?_⟩
  intro g a ϑ ha odd hom cut κ hκ hs δ b i o hm η hη inn out m screen M hM jet d A z W B ℓ e hB hℓ he hBo hBw symm field controls source
  have orderG := (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCoF) hM).trans hBo
  have orderF := (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCoG) hM).trans hBo
  have weakG := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hCwF)
    (by norm_num : (0 : ℝ) ≤ 2)) hM).trans hBw
  have weakF := (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hCwG)
    (by norm_num : (0 : ℝ) ≤ 2)) hM).trans hBw
  have hG := gauge ϑ cut κ hκ hs m (metricDensity g) a ha odd hom (gaugeFrozenContraction m) screen
    (thinScreenAngular m i o hm hη inn out).degree M hM
    (fun k I J => profileOrder_mono (Nat.le_max_left NG NF) (jet k J I).1)
    d A z W B ℓ e hB hℓ he orderG weakG symm field controls.1 controls.2.1 source controls.2.2.1 controls.2.2.2
  have hF := far g a ϑ cut κ hκ hs δ b i o hm hη inn out M hM
    (fun k J I => profileOrder_mono (Nat.le_max_right NG NF) (jet k J I).2)
    d A z W B ℓ e hB hℓ he orderF weakF symm field controls.1 controls.2.1 source controls.2.2.1 controls.2.2.2
  refine (add_le_add hG hF).trans_eq ?_
  ring

end Burnett.V11
