import Burnett.Analysis.Microlocal.CompactChartInput
import Burnett.Analysis.Microlocal.Overlap.HalfDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.F05.ChartVolumeAmplitude

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetricTransition
open Burnett.F05.ChartVolumeBridge Burnett.F05.OriginalCoordinateCurl
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.X02.SobolevTestJet (D Space)
open scoped ContDiff ENNReal Topology Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The same cutoff gradient with the fixed geometric volume half-density,
as a legitimate whole-space Lebesgue Fourier input. -/
def originalGradient_volumeWeightedL2
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hs : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) : ComplexL2 Space :=
  let ψ := chartVolumeWeightedCutoff B hs hn c χ hχ
  let hψ := (chartVolumeWeightedCutoff_tsupport B hs hn c χ hχ).trans hχ
  (originalGradientSchwartz B g hs hg c ψ hψ n i).toLp 2 volume

theorem originalGradient_volumeWeightedL2_ae
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hs : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B) (c : M)
    (χ : D) (hχ : tsupport (χ : Space → ℝ) ⊆ (chartAt CoordinateSpace c).target)
    (n : ℕ) (i : JetSlot) :
    (originalGradient_volumeWeightedL2 B g hs hg hn c χ hχ n i : Space → ℂ) =ᵐ[volume]
      fun x => (chartHalfDensity B c x : ℂ) * originalGradientSchwartz B g hs hg c χ hχ n i x := by
  let ψ := chartVolumeWeightedCutoff B hs hn c χ hχ
  let hψ := (chartVolumeWeightedCutoff_tsupport B hs hn c χ hχ).trans hχ
  let w := originalGradientSchwartz B g hs hg c ψ hψ n i
  change (w.toLp 2 volume : Space → ℂ) =ᵐ[volume] _
  filter_upwards [w.coeFn_toLp 2 volume] with x hx
  rw [hx]
  change originalGradientSchwartz B g hs hg c ψ hψ n i x = _
  rw [originalGradientSchwartz_apply, originalGradientSchwartz_apply,
    show (ψ : Space → ℝ) x = (χ : Space → ℝ) x * chartHalfDensity B c x from rfl]
  push_cast
  ring

end Burnett.F05.ChartVolumeAmplitude

namespace Burnett.Microlocal.CountableAuxiliaryCharts

open Set MeasureTheory Burnett.Fourier
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldBilinear Burnett.Geometry.ManifoldMetric
open Burnett.F05.ChartVolumeBridge Burnett.F05.ChartVolumeAmplitude Burnett.Microlocal.CurlDensity
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The ball and chart stay fixed when the compact cutoff absorbs the
geometric half-density. -/
def volumeModeInput (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (q : CompactChartInput M) : CompactChartInput M where
  center := q.center
  ball := q.ball
  ball_in_chart := q.ball_in_chart
  cutoff := chartVolumeWeightedCutoff B hB hn q.center q.cutoff (q.cutoff_support.trans q.ball_in_chart)
  cutoff_support := (chartVolumeWeightedCutoff_tsupport B hB hn q.center q.cutoff
    (q.cutoff_support.trans q.ball_in_chart)).trans q.cutoff_support

/-- Weighting the compact chart and weighting the localized original coordinate gradient
give exactly the same Lebesgue Fourier input, for every metric and ordered derivative slot. -/
theorem chartJetL2_volumeModeInput
    (B : Field (M := M)) (g : ℕ → Field (M := M))
    (hB : IsSmooth B) (hg : ∀ n, IsSmooth (g n)) (hn : IsNondegenerate B)
    (q : CompactChartInput M) (n : ℕ) (i : JetSlot) :
    chartJetL2 (volumeModeInput B hB hn q) B g hB hg n i =
      originalGradient_volumeWeightedL2 B g hB hg hn q.center q.cutoff
        (q.cutoff_support.trans q.ball_in_chart) n i := rfl

end Burnett.Microlocal.CountableAuxiliaryCharts
