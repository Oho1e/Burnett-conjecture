import Burnett.Analysis.HminusWeightedDual
import Burnett.Analysis.WeightedFourierTail

/-!
# CompactRellich

Paper-specific Hminus support; scope and remaining geometric obligations are recorded separately.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
noncomputable section

namespace Burnett.Analysis.CompactRellich
open MeasureTheory Filter
open scoped Topology ContDiff FourierTransform ENNReal
open Burnett.X02.SobolevTestJet

theorem negativeEnergy_tendsto_zero_of_commonCutoff {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => HminusWeightedDual.negativeEnergy
      (HminusWeightedDual.complexSource (f n) (hs n)
        (LocalHminusFourier.source_hasCompactSupport χ (hχ n)))) atTop (𝓝 0) := by
  change Tendsto (fun n => ∫ ξ, ‖𝓕 (fun x => (f n x : ℂ)) ξ‖^2 /
    (1 + 4 * Real.pi^2 * ‖ξ‖^2)) atTop (𝓝 0)
  exact HminusWeightedTail.weighted_fourier_energy_tendsto_zero hs hf χ hχ hB ht

theorem sourceFunctional_tendsto_zero_of_commonCutoff {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    Tendsto (fun n => HminusWeightedDual.sourceFunctional (f n) (hs n)
      (LocalHminusFourier.source_hasCompactSupport χ (hχ n))) atTop (𝓝 0) := by
  exact HminusWeightedDual.sourceFunctional_tendsto_zero hs
    (fun n => LocalHminusFourier.source_hasCompactSupport χ (hχ n))
    (negativeEnergy_tendsto_zero_of_commonCutoff hs hf χ hχ hB ht)

theorem exists_sourceFunctionals_strong_zero {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (hf : ∀ n, MemLp (f n) 2 (volume : Measure Space))
    (χ : D) (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    ∃ F : ℕ → (Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ),
      (∀ n (φ : D), F n (Burnett.X02.GraphDual.testMap J φ) =
        ∫ x, f n x * (φ : Space → ℝ) x) ∧
      Tendsto F atTop (𝓝 0) ∧ Tendsto (fun n => ‖F n‖) atTop (𝓝 0) := by
  let hc (n : ℕ) : HasCompactSupport (f n) := LocalHminusFourier.source_hasCompactSupport χ (hχ n)
  let F (n : ℕ) := HminusWeightedDual.sourceFunctional (f n) (hs n) (hc n)
  have hF : Tendsto F atTop (𝓝 0) := sourceFunctional_tendsto_zero_of_commonCutoff hs hf χ hχ hB ht
  refine ⟨F, ?_, hF, ?_⟩
  · intro n φ
    exact HminusWeightedDual.sourceFunctional_test (f n) (hs n) (hc n) φ
  · have hn : Continuous (fun H : Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ => ‖H‖) :=
      @continuous_norm (Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ) inferInstance
    simpa only [Function.comp_def, ContinuousLinearMap.opNorm_zero] using
      (hn.tendsto (0 : Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ)).comp hF

theorem exists_sourceFunctionals_of_eLpNorm_bound {f : ℕ → Space → ℝ}
    (hs : ∀ n, ContDiff ℝ ∞ (f n)) (χ : D)
    (hχ : ∀ n x, f n x ≠ 0 → (χ : Space → ℝ) x = 1)
    {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ n, eLpNorm (f n) 2 (volume : Measure Space) ≤ ENNReal.ofReal B)
    (ht : ∀ φ : D, Tendsto (fun n => ∫ x, f n x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    ∃ F : ℕ → (Burnett.X02.GraphDual.Graph J →L[ℝ] ℝ),
      (∀ n (φ : D), F n (Burnett.X02.GraphDual.testMap J φ) =
        ∫ x, f n x * (φ : Space → ℝ) x) ∧
      Tendsto F atTop (𝓝 0) ∧ Tendsto (fun n => ‖F n‖) atTop (𝓝 0) := by
  let hc (n : ℕ) : HasCompactSupport (f n) := LocalHminusFourier.source_hasCompactSupport χ (hχ n)
  let hf (n : ℕ) : MemLp (f n) 2 (volume : Measure Space) :=
    (hs n).continuous.memLp_of_hasCompactSupport (hc n)
  have hb (n : ℕ) : ‖(hf n).toLp (f n)‖ ≤ B := by
    rw [Lp.norm_toLp]
    exact ENNReal.toReal_le_of_le_ofReal hB0 (hB n)
  exact exists_sourceFunctionals_strong_zero hs hf χ hχ hb ht

end Burnett.Analysis.CompactRellich
