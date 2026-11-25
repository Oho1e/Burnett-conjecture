import Burnett.Analysis.TransportPatches.PatchLpInput
import Burnett.Analysis.TransportPatches.ActualPatchPhysicalGaugeLp

set_option autoImplicit false
set_option maxRecDepth 4400
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference
open scoped ContDiff ENNReal

/-- Entrywise whole-space bounds with the physical and gauge components
taken from the same matrix input and the same patch volume. -/
def ProjectedPatchLpBounds (p : ℝ) (z : ProjectionSchwartzMatrix)
    (K : Set CoordinateSpace) (value gradient : ℝ) : Prop :=
  let u := projectionFullSchwartz z
  let G := projectedGaugeComplement z
  let v := (volume K ^ (1 / p)).toReal
  ∀ i j : Index,
    ((eLpNorm (u i j : CoordinateSpace → ℂ) (ENNReal.ofReal p) volume).toReal ≤ value * v ∧
    (eLpNorm (G i j : CoordinateSpace → ℂ) (ENNReal.ofReal p) volume).toReal ≤ value * v) ∧
    ∀ a : Index,
      (eLpNorm (projectionMatrixDerivative a u i j : CoordinateSpace → ℂ)
        (ENNReal.ofReal p) volume).toReal ≤ gradient * v ∧
      (eLpNorm (projectionMatrixDerivative a G i j : CoordinateSpace → ℂ)
        (ENNReal.ofReal p) volume).toReal ≤ gradient * v

theorem ProjectedPatchLpBounds.mono {p : ℝ} {z : ProjectionSchwartzMatrix}
    {K : Set CoordinateSpace} {v₀ v₁ g₀ g₁ : ℝ}
    (h : ProjectedPatchLpBounds p z K v₀ g₀) (hv : v₀ ≤ v₁) (hg : g₀ ≤ g₁) :
    ProjectedPatchLpBounds p z K v₁ g₁ := by
  intro i j
  obtain ⟨⟨hu, hG⟩, hD⟩ := h i j
  have hV := mul_le_mul_of_nonneg_right hv (ENNReal.toReal_nonneg (a := volume K ^ (1 / p)))
  have hGrad := mul_le_mul_of_nonneg_right hg (ENNReal.toReal_nonneg (a := volume K ^ (1 / p)))
  exact ⟨⟨hu.trans hV, hG.trans hV⟩, fun a =>
    ⟨(hD a).1.trans hGrad, (hD a).2.trans hGrad⟩⟩

/-- The original physical and gauge fields have the same patch-volume
factor in all finite exponents used in the correction energies. -/
theorem exists_projectedPatchLp_scale (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (g g₀ : CoordinateSpace → Tensor2) (hg : SmoothCoordinateComponents g)
        (hg₀ : SmoothCoordinateComponents g₀)
        (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
        (K : Set CoordinateSpace), IsCompact K → tsupport χ ⊆ K →
      ∀ (A B D e : ℝ), 0 ≤ A → 0 ≤ B → 0 ≤ D → 0 ≤ e →
        (∀ x ∈ tsupport χ, ‖χ x‖ ≤ A) →
        (∀ x ∈ tsupport χ, ‖iteratedFDeriv ℝ 1 χ x‖ ≤ B) →
        (∀ x ∈ tsupport χ, ‖g x - g₀ x‖ ≤ e ∧
          ‖coordinateJet g x - coordinateJet g₀ x‖ ≤ D) →
        let z := localizedMetricSchwartz g g₀ χ hχ hc hg hg₀
        ProjectedPatchLpBounds p z K (C * (A * e)) (C * (A * D + B * e)) := by
  obtain ⟨C, hC, hOp⟩ := exists_projectionPhysicalGauge_entryLp_bounds p hp
  have hp₀ : 0 < p := zero_lt_one.trans hp
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro g g₀ hg hg₀ χ hχ hc K hK hSupp A B D e hA hB hD he hχ₀ hχ₁ hField z i j
  let V := volume K ^ (1 / p)
  have hV : V < ⊤ :=
    ENNReal.rpow_lt_top_of_nonneg (div_nonneg zero_le_one hp₀.le) hK.measure_lt_top.ne
  have hConvert (E M : ℝ≥0∞) {m : ℝ} (hm : 0 ≤ m)
      (hE : E ≤ C * M) (hM : M ≤ ENNReal.ofReal m * V) :
      E.toReal ≤ C.toReal * m * V.toReal := by
    have hR : C * (ENNReal.ofReal m * V) < ⊤ :=
      ENNReal.mul_lt_top hC (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV)
    have hBound := ENNReal.toReal_mono hR.ne (hE.trans (mul_le_mul_left' hM C))
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm, mul_assoc] using hBound
  obtain ⟨hZ, hZD⟩ := localizedMetricSchwartz_patchLp g g₀ hg hg₀ χ hχ hc K hK hSupp
    A B D e hA hB hD he hχ₀ hχ₁ hField p hp₀
  obtain ⟨⟨hU, hG⟩, hUGD⟩ := hOp z i j
  have hVal := mul_nonneg hA he
  have hGrad := add_nonneg (mul_nonneg hA hD) (mul_nonneg hB he)
  exact ⟨⟨hConvert _ _ hVal hU hZ, hConvert _ _ hVal hG hZ⟩, fun a =>
    ⟨hConvert _ _ hGrad (hUGD a).1 (hZD a), hConvert _ _ hGrad (hUGD a).2 (hZD a)⟩⟩

end Burnett.C03
