import Burnett.Analysis.GaugeProjection.OpenChartMetricRepresentatives
import Burnett.Analysis.GaugeProjection.LocalizedProjectedFiniteLp
import Burnett.Analysis.GaugeProjection.LocalizedProjectedUniformSmallness

set_option autoImplicit false

noncomputable section

namespace Burnett.P01

open MeasureTheory Filter Set
open Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff Topology NNReal ENNReal

/-- The norm conclusions for one fixed projected sequence, before choosing `p`. -/
structure ProjectedFieldNormLimits (u : ℕ → ProjectionSchwartzMatrix) : Prop where
  uniformlySmall : ∀ ε > (0 : ℝ), ∀ᶠ n in atTop, ∀ x a b, ‖u n a b x‖ < ε
  linfinity : Tendsto (fun n => eLpNorm (fun x : CoordinateSpace => fun a b => u n a b x)
    ⊤ volume) atTop (𝓝 0)
  finiteLp : ∀ p : ℝ, 1 < p →
    Tendsto (fun n => projectionMatrixLpNorm p (u n)) atTop (𝓝 0) ∧
      ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ n, projectionGradientLpNorm p (u n) ≤ C

/-- Zero-extend the actual cutoff fluctuation of locally smooth chart components.
All the projected norm statements use the same Schwartz input sequence. -/
theorem exists_openChartProjectedField_norms {U : Set CoordinateSpace} (hU : IsOpen U)
    (g : ℕ → CoordinateSpace → Tensor2) (g₀ : CoordinateSpace → Tensor2)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχU : tsupport χ ⊆ U)
    (hConv : TendstoUniformlyOn g g₀ atTop (tsupport χ))
    (B : ℝ≥0) (hDeriv : ∀ n i j x, x ∈ tsupport χ →
      ‖fderiv ℝ (fun y => g n y i j - g₀ y i j) x‖ ≤ (B : ℝ)) :
    ∃ z : ℕ → ProjectionSchwartzMatrix,
      (∀ n x i j, z n i j x = ((χ x * (g n x i j - g₀ x i j) : ℝ) : ℂ)) ∧
      ProjectedFieldNormLimits (fun n => projectionFullSchwartz (z n)) := by
  obtain ⟨G, G₀, hG, hG₀, nearG, nearG₀⟩ :=
    exists_openChartMetricRepresentatives hχc hU hχU g g₀ hg hg₀
  have agrees (n : ℕ) (x : CoordinateSpace) (hx : x ∈ tsupport χ) :
      G n =ᶠ[𝓝 x] g n := (nearG n).filter_mono (nhds_le_nhdsSet hx)
  have agrees₀ (x : CoordinateSpace) (hx : x ∈ tsupport χ) :
      G₀ =ᶠ[𝓝 x] g₀ := nearG₀.filter_mono (nhds_le_nhdsSet hx)
  have hConvG : TendstoUniformlyOn G G₀ atTop (tsupport χ) :=
    (hConv.congr (Eventually.of_forall fun n x hx => (agrees n x hx).eq_of_nhds.symm)).congr_right
      (fun x hx => (agrees₀ x hx).eq_of_nhds.symm)
  have hDerivG : ∀ n i j x, x ∈ tsupport χ →
      ‖fderiv ℝ (fun y => G n y i j - G₀ y i j) x‖ ≤ (B : ℝ) := by
    intro n i j x hx
    have differenceAgrees : (fun y => G n y i j - G₀ y i j) =ᶠ[𝓝 x]
        (fun y => g n y i j - g₀ y i j) := by
      filter_upwards [agrees n x hx, agrees₀ x hx] with y hy hy₀
      rw [hy, hy₀]
    rw [differenceAgrees.fderiv_eq]
    exact hDeriv n i j x hx
  let z := fun n => localizedMetricSchwartz (G n) G₀ χ hχ hχc (hG n) hG₀
  refine ⟨z, ?_, ?_⟩
  · intro n x i j
    change ((χ x * (G n x i j - G₀ x i j) : ℝ) : ℂ) = _
    by_cases hx : x ∈ tsupport χ
    · rw [(agrees n x hx).eq_of_nhds, (agrees₀ x hx).eq_of_nhds]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  · obtain ⟨hSmall, hTop⟩ := localizedMetricProjection_uniformly_small
      G G₀ hG hG₀ χ hχ hχc hConvG B hDerivG
    exact ⟨hSmall, hTop, fun p hp => localizedMetricProjection_finiteLp_norms
      G G₀ hG hG₀ χ hχ hχc hConvG B hDerivG p hp⟩

end Burnett.P01
