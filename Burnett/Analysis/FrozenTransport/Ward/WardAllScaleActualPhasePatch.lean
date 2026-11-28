import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleActualLowFields
import Burnett.Analysis.FrozenTransport.UniformThinCubicPatch
import Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Set Burnett.Fourier Burnett.A05 Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz)
open Burnett.C03 (ProjectedPatchLpBounds projectedGaugeComplement)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped ContDiff Topology

open private cubic_product_tail from Burnett.Analysis.FrozenTransport.UniformThinCubicPatch
open private fieldGradientL3_sub_le from Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms

/-- The common cap/phase estimate on the fixed original C02 patch. Every
component satisfying the actual phase-gradient estimate uses those same
two full-space C02 differences and one genuine C03 source. -/
theorem wardActualPhaseComponent_patch_bound (m : Tensor2) (physical : Fin 3 → Bool) (k : Fin 3 → OrderedPair)
    (F : Joint → ℂ) (C : ℝ) (hC : 0 ≤ C) (hForm : WardActualLowComponentBound m physical k F C)
    (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
    (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E) (value : ℕ → ℝ) (grad Ce ell alpha : ℝ)
    (hCe : 0 ≤ Ce) (hEll : 0 < ell) (hEll₁ : ell ≤ 1) (hAlpha : 0 ≤ alpha)
    (hv : Tendsto value atTop (𝓝 0)) (hSource : ∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) :
    let mass := ((volume : Measure E) P).toReal
    let M := mass ^ (1 / 3 : ℝ)
    let T := actualThinScreenMultiplier m wi wo hm hη i o
    let diff (n : ℕ) (b : Index × OrderedPair) :=
      multiplierCoordinateDerivative originalProjectedMatrixMultiplier (z n) b.1 b.2 -
        multiplierCoordinateDerivative T (z n) b.1 b.2
    let phase (n : ℕ) (b : Index × OrderedPair) := fourierMultiplier (frozenPhaseScalar m)
      (multiplierCoordinateDerivative T (z n) b.1 b.2)
    (∀ ε > 0, ∀ᶠ n in atTop,
      (eLpNorm (orderedGradientValue (diff n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε ∧
      (eLpNorm (orderedGradientValue (phase n)) 3 volume).toReal ≤ Ce * ell ^ alpha * M + ε) →
    let f (n : ℕ) := wardActualLowSlots m wi wo hm hη i o (z n) physical k
    ∀ ε > 0, ∀ᶠ n in atTop, ‖radianTrilinearForm F (f n 0) (f n 1) (f n 2)‖ ≤
      (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  intro mass M T diff phase hRate f
  let U (n : ℕ) (b : OrderedPair) := projectionFullSchwartz (z n) b.1 b.2
  let G (n : ℕ) (b : OrderedPair) := projectedGaugeComplement (z n) b.1 b.2
  let V (n : ℕ) := actualThinSchwartzField m wi wo hm hη i o (z n)
  let W (n : ℕ) := actualWardPhaseSchwartz m wi wo hm hη i o (z n)
  let A (n : ℕ) := euclideanFieldGradientL3 (W n)
  let B (n : ℕ) := euclideanFieldGradientL3 (G n) + euclideanFieldGradientL3 (V n)
  let error (n : ℕ) := ‖radianTrilinearForm F (f n 0) (f n 1) (f n 2)‖
  have hN (u : OrderedPair → SchwartzMap E ℂ) : 0 ≤ euclideanFieldGradientL3 u := ENNReal.toReal_nonneg
  have hE (n : ℕ) : error n ≤ C * A n * (B n)^2 := (hForm wi wo hm η hη i o (z n)).2
  have hm₀ : 0 ≤ mass := ENNReal.toReal_nonneg
  have hM₀ : 0 ≤ M := Real.rpow_nonneg hm₀ _
  have hEllPow : ell ^ alpha ≤ 1 := Real.rpow_le_one hEll.le hEll₁ hAlpha
  have hCeScale : Ce * ell ^ alpha * M ≤ Ce * M := by
    exact mul_le_mul_of_nonneg_right (by simpa using mul_le_mul_of_nonneg_left hEllPow hCe) hM₀
  have hA : ∀ ε > 0, ∀ᶠ n in atTop, A n ≤ Ce * ell ^ alpha * M + ε := by
    intro ε hε
    filter_upwards [hRate ε hε] with n hn
    change euclideanFieldGradientL3 (actualWardPhaseSchwartz m wi wo hm hη i o (z n)) ≤ _
    rw [actualWardPhaseSchwartz_gradientL3]
    exact hn.2
  obtain ⟨_,_,_,hBudget⟩ := actualLinearFields_C03_budget m wi wo hm hη i o z P value grad hv hSource
  have hB : ∀ ε > 0, ∀ᶠ n in atTop, B n ≤ (128 * grad + Ce) * M + ε := by
    intro ε hε
    filter_upwards [hBudget,hRate ε hε] with n hb hd
    have hThin := fieldGradientL3_sub_le (U n) (U n - V n)
    rw [sub_sub_cancel] at hThin
    have hDiff : euclideanFieldGradientL3 (U n - V n) ≤ Ce * ell ^ alpha * M + ε :=
      (actualThinSchwartz_cubicGradientDifference m wi wo hm hη i o (z n)).le.trans hd.1
    dsimp [B]
    linarith only [hThin, hDiff, hb.1, hb.2, hCeScale]
  have hTail := cubic_product_tail error A B C (Ce * ell ^ alpha * M) ((128 * grad + Ce) * M)
    hC (mul_nonneg (mul_nonneg hCe (Real.rpow_nonneg hEll.le _)) hM₀)
    (fun n => add_nonneg (hN _) (hN _)) hE hA hB
  have hMass : M * M^2 = mass := by
    dsimp [M]
    rw [pow_two, ← Real.rpow_add_of_nonneg hm₀ (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3), ← Real.rpow_add_of_nonneg hm₀
        (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3 + 1 / 3)]
    rw [show (1 / 3 : ℝ) + (1 / 3 + 1 / 3) = 1 by norm_num, Real.rpow_one]
  have hScale : C * (Ce * ell ^ alpha * M) * ((128 * grad + Ce) * M)^2 =
      (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass := by
    rw [← hMass]
    ring
  simpa only [error, hScale] using hTail

end Burnett.C02
