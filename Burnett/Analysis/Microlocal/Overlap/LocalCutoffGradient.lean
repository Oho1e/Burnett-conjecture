import Burnett.Analysis.Microlocal.BesselLocalization
import Burnett.Analysis.Microlocal.VolumeWeightedChartJet

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.F05.ChartVolumeAmplitude Burnett.F05.ChartVolumeBridge Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.BesselLocalization (physicalCoefficient)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D Space)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- Multiplying the original cutoff multiplies each volume-weighted
ordered gradient slot by the same physical symbol. -/
theorem originalGradient_volumeWeightedL2_of_cutoff_mul
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hnB : IsNondegenerate B) (c : M)
    (χ χ' θ : D)
    (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hχ' : tsupport (χ' : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (hCut : ∀ x : Space, (χ' : Space → ℝ) x = (θ : Space → ℝ) x * (χ : Space → ℝ) x)
    (n : ℕ) (i : JetSlot) :
    originalGradient_volumeWeightedL2 B g hB hg hnB c χ' hχ' n i =
      symbolCLM (physicalCoefficient θ) (originalGradient_volumeWeightedL2 B g hB hg hnB c χ hχ n i) := by
  let u := originalGradient_volumeWeightedL2 B g hB hg hnB c χ hχ n i
  let v := originalGradient_volumeWeightedL2 B g hB hg hnB c χ' hχ' n i
  change v = symbolL2 (physicalCoefficient θ) u
  apply Lp.ext
  filter_upwards [originalGradient_volumeWeightedL2_ae B g hB hg hnB c χ' hχ' n i,
    symbolL2_ae (physicalCoefficient θ) u,
    originalGradient_volumeWeightedL2_ae B g hB hg hnB c χ hχ n i] with x hv hm hu
  rw [hv, hm, hu, originalGradientSchwartz_apply, originalGradientSchwartz_apply, hCut x]
  simp only [physicalCoefficient]
  push_cast
  ring

end Burnett.Microlocal.Overlap
