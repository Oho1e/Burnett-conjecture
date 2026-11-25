import Burnett.Analysis.TransportPatches.WideBaselineL2
import Burnett.Analysis.TransportPatches.OriginalProjectedPatchSource

/-! Identify the C03 source witness and both endpoint bounds with the C02 chart field. -/
set_option autoImplicit false
set_option maxRecDepth 4800
set_option maxHeartbeats 4700000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open ConnectionDifference ManifoldMetric ManifoldBilinear MaximalChart
open Burnett.Microlocal.AtlasVolumeGradient (fixedPerturbation)
open Burnett.P01 (ProjectionSchwartzMatrix receivingCutoffFluctuation)
open Burnett.C03 (ProjectedPatchLpBounds)
open Burnett.X02.SobolevTestJet (D)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]
  [SecondCountableTopology M]

/-- The pointwise entry of the C03 witness identifies the original centered
Schwartz input exactly, including its extension outside the patch. -/
theorem receivingCutoffFluctuation_eq_originalSourceInput
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (n : ℕ) (z : ProjectionSchwartzMatrix)
    (hz : ∀ i k x, z i k x = (((χ : E → ℝ) x *
      (metricComponents (fixedForm (g n) c) x i k - metricComponents (fixedForm B c) x i k)) : ℝ)) :
    receivingCutoffFluctuation B g hB hg c χ hχ n = z := by
  funext i k
  apply SchwartzMap.ext
  intro x
  change ((((χ : E → ℝ) x * fixedPerturbation B (g n) c x i k) : ℝ) : ℂ) = z i k x
  exact (hz i k x).symm

/-- Consume one selected C03 source witness. With the patch scale fixed,
the factor `1 + e n / ℓ` is eventually bounded by two on the same refinement. -/
theorem eventually_receivingProjectedPatchLp_of_source
    (B : Field (M := M)) (g : ℕ → Field (M := M)) (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n))
    (c : AtlasChart M) (χ : D) (hχ : tsupport (χ : E → ℝ) ⊆ c.chart.target)
    (P : Set E) (ℓ : ℝ) (hℓ : 0 < ℓ) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (e : ℕ → ℝ) (he : Tendsto e atTop (𝓝 0))
    (Cₚ : {p : ℝ // 1 < p} → ℝ) (hCₚ : ∀ p, 0 ≤ Cₚ p)
    (hSource : ∀ᶠ n in atTop, ∃ z : ProjectionSchwartzMatrix,
      (∀ i k x, z i k x = (((χ : E → ℝ) x *
        (metricComponents (fixedForm (g n) c) x i k - metricComponents (fixedForm B c) x i k)) : ℝ)) ∧
      (∀ p : {p : ℝ // 1 < p},
        ProjectedPatchLpBounds p.val z P (Cₚ p * e n) (Cₚ p * (1 + e n / ℓ)))) :
    ∀ᶠ n in atTop, ∀ p : {p : ℝ // 1 < p},
      ProjectedPatchLpBounds p.val (receivingCutoffFluctuation B g hB hg c χ hχ (σ n)) P
        (Cₚ p * e (σ n)) (2 * Cₚ p) := by
  have hE := (he.comp hσ.tendsto_atTop).eventually (Iio_mem_nhds hℓ)
  filter_upwards [hσ.tendsto_atTop.eventually hSource, hE] with n hn hE
  obtain ⟨z, hz, hBound⟩ := hn
  rw [receivingCutoffFluctuation_eq_originalSourceInput B g hB hg c χ hχ (σ n) z hz]
  intro p
  have hRatio : e (σ n) / ℓ ≤ 1 := (div_le_iff₀ hℓ).2 (by simpa only [one_mul] using hE.le)
  apply ProjectedPatchLpBounds.mono (hBound p) le_rfl
  rw [mul_comm (2 : ℝ)]
  exact mul_le_mul_of_nonneg_left (by linarith) (hCₚ p)

end Burnett.C02
