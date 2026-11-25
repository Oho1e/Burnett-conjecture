import Burnett.Analysis.TransportPatches.QuantitativeSourceRemainder
import Burnett.Analysis.TransportPatches.ProjectedSourcePatchMeasure
import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-! The exact C03 cutoff losses applied to the full-space projected raw
source, with the outer patch measure kept explicit. -/
set_option autoImplicit false
set_option maxRecDepth 3800
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.C03

open Set MeasureTheory Burnett.P01 Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped ENNReal ContDiff

private theorem norm_scalarPartial_le_first (χ : CoordinateSpace → ℝ) (x : CoordinateSpace) (a : Index) :
    ‖scalarPartial χ a x‖ ≤ ‖iteratedFDeriv ℝ 1 χ x‖ := by
  have h := (fderiv ℝ χ x).le_opNorm (EuclideanSpace.single a 1)
  simpa only [scalarPartial, EuclideanSpace.norm_single, norm_one, mul_one,
    ← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero] using h

private theorem norm_scalarPartial2_le_second (χ : CoordinateSpace → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (x : CoordinateSpace) (a b : Index) :
    ‖scalarPartial (scalarPartial χ b) a x‖ ≤ ‖iteratedFDeriv ℝ 2 χ x‖ := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ χ) := hχ.fderiv_right (by simp)
  have hApply := norm_iteratedFDeriv_clm_apply_const
    (c := EuclideanSpace.single b (1 : ℝ)) (x := x) (n := 1) hD.contDiffAt (by simp)
  have hBound : ‖iteratedFDeriv ℝ 1 (scalarPartial χ b) x‖ ≤
      ‖iteratedFDeriv ℝ 2 χ x‖ := by
    simpa only [scalarPartial, EuclideanSpace.norm_single, norm_one, one_mul,
      norm_iteratedFDeriv_fderiv] using hApply
  exact (norm_scalarPartial_le_first (scalarPartial χ b) x a).trans hBound

/-- Quantitative bound for the true projected raw source on the entire
space. The constant is selected before the patch, its scale, the inverse
extension and the metric input. -/
theorem exists_projectedRawSource_scale_bound
    (B : ℝ) (C : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ℓ : ℝ), 0 < ℓ → ∀ (χ : CoordinateSpace → ℝ)
      (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ) (Kpatch : Set CoordinateSpace),
      IsCompact Kpatch → tsupport χ ⊆ Kpatch →
      (∀ k x, x ∈ tsupport χ → ‖iteratedFDeriv ℝ k χ x‖ ≤ C k * ℓ⁻¹ ^ k) →
      ∀ (inv g g₀ : CoordinateSpace → Tensor2)
        (hi : SmoothCoordinateComponents inv) (hg : SmoothCoordinateComponents g)
        (hg₀ : SmoothCoordinateComponents g₀),
        (∀ x ∈ tsupport χ, IsSymmetricTensor (inv x)) →
        (∀ x, IsSymmetricTensor (g x)) →
        (∀ x ∈ tsupport χ, ∀ i j, coordinateRicci
          (fun y => christoffel (inv y) (coordinateJet g y)) x i j = 0) →
        (∀ x ∈ tsupport χ, ‖localizedSourceJets inv g g₀ x‖ ≤ B) →
        ∀ e : ℝ, 0 ≤ e → (∀ x ∈ tsupport χ, ‖g x - g₀ x‖ ≤ e) →
          ‖projectionFullL2 (projectionMatrixToL2
            (localizedWaveSourceSchwartz inv g g₀ χ hχ hc hi hg hg₀))‖ ≤
            ‖projectionFullL2‖ *
              (ENNReal.ofReal (M * (1 + ℓ⁻¹ + (ℓ⁻¹)^2 * e)) *
                volume Kpatch ^ ((1 : ℝ) / 2)).toReal := by
  obtain ⟨M, hM, hBound⟩ := exists_localizedSourceRemainder_scale_bound
    B (C 0) (C 1) (C 2) (hC 0) (hC 1) (hC 2)
  refine ⟨M, hM, ?_⟩
  intro ℓ hℓ χ hχ hc Kpatch hK hCover hCut inv g g₀ hi hg hg₀ hInvSym hSym hVac hJet e he hError
  apply norm_projectedLocalizedSource_le_patch_measure g inv g₀ χ hχ hc hg hi hg₀
    hInvSym hSym hVac Kpatch hK hCover _ (by positivity)
  intro x hx
  apply hBound ℓ hℓ χ x
  · simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using hCut 0 x hx
  · intro i
    exact (norm_scalarPartial_le_first χ x i).trans (by simpa only [pow_one] using hCut 1 x hx)
  · intro a b
    exact (norm_scalarPartial2_le_second χ hχ x a b).trans (hCut 2 x hx)
  · exact fun a b => (hg a b).differentiable (by simp) x
  · exact fun a b => (hg₀ a b).differentiable (by simp) x
  · exact hJet x hx
  · exact he
  · exact hError x hx

end Burnett.C03
