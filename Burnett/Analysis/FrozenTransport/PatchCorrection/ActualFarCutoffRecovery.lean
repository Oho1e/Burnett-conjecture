import Burnett.Analysis.FrozenTransport.PatchCorrection.ActualFarPatchEnvelope

set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V10.OriginalGaugeCompatibility

open Set Filter MeasureTheory Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.C02
open Burnett.Analysis.TransportWardSymbol (Mat inverseMatrix)
open Burnett.Analysis.ProjectiveNullCaps (Vec)
open Burnett.A02.FrequencySplit (E radianFourier)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.V11 (GaugeProfileBound)
open scoped ContDiff ENNReal Topology Matrix.Norms.Elementwise

/-- At fixed original fields, both upper frequency cutoffs are removed in
each finite angular sum. Exhausting the angular modes recovers the exact
tested physical correction. The forward and adjoint operator-norm tails
are those of the same `OriginalAngularCutoff`. -/
theorem exists_actualFar_cutoff_recovery :
    ∃ (N : ℕ) (C₀ C₁ : ℝ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ (g : Mat) (a : Vec → ℝ) (ϑ : ℝ → ℝ), (∀ s : ℝ, 1 ≤ s → ϑ s = 0) →
      ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ δ b i o : ℝ,
      ∀ (hm : WideScreenFrequencySmooth i o (inverseMatrix g)) {η : ℝ} (hη : 0 < η) (inn out : ℝ),
      ∀ (k J I : OrderedPair) (M : ℝ), 0 ≤ M →
      let F := actualFarAngularProfile g a ϑ κ δ b i o hm hη inn out k J I
      GaugeProfileBound N M F →
      ∃ P : OriginalAngularCutoff correctionInputWindow correctionRatioWindow F M C₀ C₁,
      ∀ z : ProjectionSchwartzMatrix, let H := projectionFullSchwartz z k.1 k.2
      ∀ u w : SchwartzMap E ℂ,
        inner ℂ (w.toLp 2 volume) (P.fullForward H u) =
          radianHighPair (actualFarRadianKernel g a ϑ κ δ b i o hm hη inn out k J I) H u w ∧
        (∀ L : ℕ, Tendsto (fun Λ : ℝ => weakConstantWaveCommutatorPair (inverseMatrix g)
          (symmetricUpperCutoffOutput (P.partialForward L H) Λ) u w) atTop
          (𝓝 (weakConstantWaveCommutatorPair (inverseMatrix g) (P.partialForward L H) u w))) ∧
        Tendsto (fun L : ℕ => weakConstantWaveCommutatorPair (inverseMatrix g) (P.partialForward L H) u w) atTop
          (𝓝 (weakConstantWaveCommutatorPair (inverseMatrix g) (P.fullForward H) u w)) := by
  obtain ⟨N, C₀, C₁, _, hC₀, hC₁, expansion⟩ := exists_originalAngular_hermitian_angular_cutoff
    correctionInputWindow correctionRatioWindow (r := 1 / 2) (ρ := 1 / 4) (R := 1)
    (by norm_num) (by norm_num) (by norm_num) le_rfl correctionInputWindow_smooth
    correctionInputWindow_zero correctionInputWindow_one correctionRatioWindow_smooth correctionRatioWindow_zero
  refine ⟨N, C₀, C₁, hC₀, hC₁, ?_⟩
  intro g a ϑ cutoff κ hκ hs δ b i o hm η hη inn out k J I M hM F bounds
  obtain ⟨V, hV, sub, smooth, jet⟩ := bounds
  obtain ⟨P⟩ := expansion hV sub smooth M hM (fun n hn p hp x => jet n hn (p, (x : E)) ⟨hp, x.property⟩)
  refine ⟨P, ?_⟩
  intro z H u w
  have low (p : E) (hp : ‖p‖ ≤ 1) : radianFourier H p = 0 := by
    simp [H, projectionFullSchwartz_radianFourier, regularizedComplexGaugeProjection, gaugeProjectionInfrared_zero hp]
  exact ⟨(P.fullPairs H u w).1.trans (actualFarA08_pair g a ϑ cutoff κ hκ hs δ b i o hm hη inn out k J I H low u w).symm,
    P.mixedWavePair_cutoff_recovery (inverseMatrix g) H u w⟩

end Burnett.V10.OriginalGaugeCompatibility
