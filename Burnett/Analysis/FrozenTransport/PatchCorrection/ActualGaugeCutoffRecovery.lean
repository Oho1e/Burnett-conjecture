import Burnett.Analysis.FrozenTransport.PatchCorrection.OriginalGaugePatchEnvelope

set_option autoImplicit false
set_option maxHeartbeats 4100000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V11

open Set Filter MeasureTheory Matrix Burnett.A06 Burnett.A07 Burnett.A08 Burnett.P01 Burnett.V08
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff ENNReal Topology Matrix

/-- Both upper cutoffs and the angular truncation are removed with the
original gauge low field and both original high slots fixed. -/
theorem exists_actualGauge_cutoff_recovery :
    ∃ (N : ℕ) (C₀ C₁ : ℝ), 0 ≤ C₀ ∧ 0 ≤ C₁ ∧
      ∀ (ϑ : ℝ → ℝ), (∀ s : ℝ, 1 ≤ s → ϑ s = 0) →
      ∀ (κ : ℝ), 0 < κ → κ < 1 / 16 → ∀ (m : Fin 4 → Fin 4 → ℝ) (ρ : ℝ) (a : E → ℝ),
      ContDiffOn ℝ ∞ a {x : E | x ≠ 0} → (∀ x, a (-x) = -a x) →
      (∀ s : ℝ, 0 < s → ∀ x, a (s • x) = s * a x) →
      ∀ (C : Matrix TensorSlot TensorSlot ℝ) (S : GaugeScreen), (∀ t : ℝ, 0 < t → ∀ x, S (t • x) = S x) →
      ∀ (k I J : TensorSlot) (M : ℝ), 0 ≤ M →
      let F := gaugeTriadAngularProfile ϑ κ m ρ a C S k I J
      GaugeProfileBound N M F →
      ∃ P : OriginalAngularCutoff gaugeCorrectionInfrared gaugeRatioGuard F M C₀ C₁,
      ∀ z : ProjectionSchwartzMatrix, let H := Burnett.C03.projectedGaugeComplement z k.1 k.2
      ∀ u w : SchwartzMap E ℂ,
        inner ℂ (w.toLp 2 volume) (P.fullForward H u) =
          radianHighPair (gaugeRawEntry ϑ gaugeCorrectionInfrared gaugeCorrectionInfrared κ m ρ a C S k I J) H u w ∧
        (∀ L : ℕ, Tendsto (fun Λ : ℝ => weakConstantWaveCommutatorPair m
          (symmetricUpperCutoffOutput (P.partialForward L H) Λ) u w) atTop
          (𝓝 (weakConstantWaveCommutatorPair m (P.partialForward L H) u w))) ∧
        Tendsto (fun L : ℕ => weakConstantWaveCommutatorPair m (P.partialForward L H) u w) atTop
          (𝓝 (weakConstantWaveCommutatorPair m (P.fullForward H) u w)) := by
  obtain ⟨N, C₀, C₁, _, hC₀, hC₁, expansion⟩ := exists_originalAngular_hermitian_angular_cutoff
    gaugeCorrectionInfrared gaugeRatioGuard (r := 1 / 2) (ρ := 1 / 4) (R := 1)
    (by norm_num) (by norm_num) (by norm_num) le_rfl gaugeCorrectionInfrared_smooth
    gaugeCorrectionInfrared_zero gaugeCorrectionInfrared_one gaugeRatioGuard_smooth
    (fun _ h => gaugeRatioGuard_vanishes h)
  refine ⟨N, C₀, C₁, hC₀, hC₁, ?_⟩
  intro ϑ cut κ hκ hs m ρ a ha hodd hhom C S degree k I J M hM F bounds
  obtain ⟨V, hV, sub, smooth, jet⟩ := bounds
  obtain ⟨P⟩ := expansion hV sub smooth M hM (fun n hn p hp x => jet n hn (p, (x : E)) ⟨hp, x.property⟩)
  refine ⟨P, ?_⟩
  intro z H u w
  exact ⟨(P.fullPairs H u w).1.trans
    (actualGaugeA08_pair ϑ cut κ hκ hs m ρ a ha hodd hhom C S degree k I J H (gaugeLow_spectrum_zero z k) u w).symm,
    P.mixedWavePair_cutoff_recovery m H u w⟩

end Burnett.V11
