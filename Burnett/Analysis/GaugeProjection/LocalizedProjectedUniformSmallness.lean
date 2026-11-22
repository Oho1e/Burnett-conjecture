import Burnett.Analysis.GaugeProjection.ProjectedUniformSmallness
import Burnett.Analysis.GaugeProjection.LocalizedMetricSchwartzInputs

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology NNReal ENNReal

/-- The projected cutoff metric fluctuation converges uniformly on the whole
coordinate space and in the matrix-valued L∞ norm. -/
theorem localizedMetricProjection_uniformly_small
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n, SmoothCoordinateComponents (g n)) (hg₀ : SmoothCoordinateComponents g₀)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (B : ℝ≥0) (hDeriv : ∀ n i j x, x ∈ tsupport χ →
      ‖fderiv ℝ (fun y => g n y i j - g₀ y i j) x‖ ≤ (B : ℝ)) :
    let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
    (∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x a b, ‖projectionFullSchwartz (z n) a b x‖ < ε) ∧
    Tendsto (fun n => eLpNorm (fun x : CoordinateSpace => fun a b =>
      projectionFullSchwartz (z n) a b x) ⊤ volume) atTop (𝓝 0) := by
  let z := fun n => localizedMetricSchwartz (g n) g₀ χ hχ hc (hg n) hg₀
  obtain ⟨L, hL, hSmall⟩ := localizedMetricSchwartz_uniform_inputs g g₀ hg hg₀
    χ hχ hc hConv B hDeriv
  exact ⟨projectionFullSchwartz_uniformly_small z L hL hSmall,
    projectionFullSchwartz_eLpNorm_top_tendsto_zero z L hL hSmall⟩

end Burnett.P01
