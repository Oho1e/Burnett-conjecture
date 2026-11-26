import Burnett.Analysis.TransportPatches.PatchCorrectionGradientNorms
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

set_option autoImplicit false

noncomputable section

namespace Burnett.C03

open MeasureTheory Burnett.P01 Burnett.RicciSymbol Burnett.A08
open Burnett.Geometry.ConnectionDifference
open Burnett.A07 (coordinateDerivative highDerivativeLp4Sum)
open scoped ENNReal BigOperators

/-- The component norms in the complete scalar correction at the physical
and gauge entries of a single projected original patch. -/
theorem projectedPatch_correctionLpBudget
    {z : ProjectionSchwartzMatrix} {W : Set CoordinateSpace} {value₂ value gradient₂ gradient₄ : ℝ}
    (h₂ : ProjectedPatchLpBounds 2 z W value₂ gradient₂)
    (h₄ : ProjectedPatchLpBounds 4 z W value gradient₄)
    (i j : Index) :
    let u := projectionFullSchwartz z
    let G := projectedGaugeComplement z
    let V := (volume W).toReal
    schwartzGradientNorm 2 (u i j) ≤ (4 * gradient₂) * V ^ ((1 : ℝ) / 2) ∧
    highDerivativeLp4Sum (u i j) ≤ (4 * gradient₄) * V ^ ((1 : ℝ) / 4) ∧
    ∀ k l : Index,
      (‖(u k l).toLp 4 volume‖ ≤ value * V ^ ((1 : ℝ) / 4) ∧
        ‖(G k l).toLp 4 volume‖ ≤ value * V ^ ((1 : ℝ) / 4)) ∧
      (schwartzGradientNorm 4 (u k l) ≤ (4 * gradient₄) * V ^ ((1 : ℝ) / 4) ∧
        schwartzGradientNorm 4 (G k l) ≤ (4 * gradient₄) * V ^ ((1 : ℝ) / 4)) := by
  have hTwo : ENNReal.ofReal (2 : ℝ) = 2 := by norm_num
  have hFour : ENNReal.ofReal (4 : ℝ) = 4 := by norm_num
  simp only [ENNReal.toReal_rpow]
  refine ⟨?_, ?_, ?_⟩
  · simpa only [hTwo] using
      (projectedPatchLp_gradients (by norm_num : (1 : ℝ) < 2) h₂ i j).1
  · unfold highDerivativeLp4Sum
    calc
      _ ≤ ∑ _ : Index, gradient₄ * (volume W ^ ((1 : ℝ) / 4)).toReal := by
        apply Finset.sum_le_sum
        intro a _
        rw [SchwartzMap.toLp, Lp.norm_toLp]
        simpa only [projectionMatrixDerivative, hFour] using ((h₄ i j).2 a).1
      _ = _ := by simp [nsmul_eq_mul, mul_assoc]
  · intro k l
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [SchwartzMap.toLp, Lp.norm_toLp]
      simpa only [hFour] using (h₄ k l).1.1
    · rw [SchwartzMap.toLp, Lp.norm_toLp]
      simpa only [hFour] using (h₄ k l).1.2
    · simpa only [hFour] using
        projectedPatchLp_gradients (by norm_num : (1 : ℝ) < 4) h₄ k l

end Burnett.C03
