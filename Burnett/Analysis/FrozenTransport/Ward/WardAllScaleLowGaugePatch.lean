import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleLowGaugePhase
import Burnett.Analysis.FrozenTransport.UniformThinCubicPatch
import Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms

set_option autoImplicit false
set_option maxRecDepth 6500
set_option maxHeartbeats 12500000
noncomputable section

namespace Burnett.C02

open Filter MeasureTheory Set Burnett.Fourier Burnett.A02.FrequencySplit Burnett.Analysis.CapFourier
open Burnett.RicciSymbol (Index Tensor2)
open Burnett.P01 (ProjectionSchwartzMatrix projectionFullSchwartz)
open Burnett.C03 (ProjectedPatchLpBounds projectedGaugeComplement)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.A07 (coordinateDerivative)
open scoped ContDiff Topology

open private cubic_product_tail from Burnett.Analysis.FrozenTransport.UniformThinCubicPatch
open private fieldGradientL3_sub_le from Burnett.Analysis.FrozenTransport.OriginalCubicPatchNorms

private theorem ward_coordinate_gradient_bound (f : OrderedPair → SchwartzMap E ℂ) (k : OrderedPair) :
    wardCoordinateGradientL3 (f k) ≤ 4 * euclideanFieldGradientL3 f := by
  have hComponent (i : Fin 4) :
      (eLpNorm (coordinateDerivative i (f k) : E → ℂ) 3 volume).toReal ≤ euclideanFieldGradientL3 f := by
    have h₃ : ENNReal.ofReal (3 : ℝ) = 3 := by norm_num
    have hGrad (x : E) : ‖coordinateDerivative i (f k) x‖ ≤ ‖euclideanFieldGradient f x‖ :=
      PiLp.norm_apply_le (euclideanFieldGradient f x) (i,k)
    have hFin := euclideanFieldGradientNorm_lt_top f
    unfold euclideanFieldGradientL3
    exact ENNReal.toReal_mono hFin.ne (by
      simpa only [euclideanFieldGradientNorm, h₃] using eLpNorm_mono hGrad)
  calc
    _ ≤ ∑ _i : Fin 4, euclideanFieldGradientL3 f :=
      Finset.sum_le_sum fun i _ => hComponent i
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]

/-- A fixed original subpatch, its original projected and gauge-complement
fields, and its two already-proved estimates give the exact cubic volume
power for the middle low-gauge Ward summand. -/
theorem exists_actualWardLowGaugeMiddleComponent_patch_bound (ϑ : ℝ → ℝ) (hϑ : ContDiff ℝ ∞ ϑ)
    (hCut : ∀ t, 1 ≤ t → ϑ t = 0) (κ : ℝ) (hκ : 0 < κ) (hSmall : κ < 1 / 16)
    (m : Tensor2) (w : ℝ) (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ) (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (k l j : OrderedPair) : ∃ C : ℝ, 0 ≤ C ∧
      ∀ (wi wo : ℝ) (hm : WideScreenFrequencySmooth wi wo m) (η : ℝ) (hη : 0 < η)
        (i o : ℝ) (z : ℕ → ProjectionSchwartzMatrix) (P : Set E)
        (value : ℕ → ℝ) (grad Ce ell alpha : ℝ),
      0 ≤ grad → 0 ≤ Ce → 0 < ell → ell ≤ 1 → 0 ≤ alpha →
      Tendsto value atTop (𝓝 0) →
      (∀ᶠ n in atTop, ProjectedPatchLpBounds 3 (z n) P (value n) grad) →
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
      let V (n : ℕ) := actualThinSchwartzField m wi wo hm hη i o (z n)
      let G (n : ℕ) := projectedGaugeComplement (z n) k.1 k.2
      let F := wardLowGaugeMiddleSymbol ϑ κ m w a (wardTensorBasis k) (wardTensorBasis l) (wardTensorBasis j)
      ∀ ε > 0, ∀ᶠ n in atTop, ‖radianTrilinearForm F (G n) (V n l) (V n j)‖ ≤
        (C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass + ε := by
  obtain ⟨C,hC,hForm⟩ := exists_actualWardLowGaugeMiddleComponent_bound ϑ hϑ hCut κ hκ hSmall m w a ha hOdd hHom k l j
  refine ⟨128 * C,mul_nonneg (by norm_num) hC,?_⟩
  intro wi wo hm η hη i o z P value grad Ce ell alpha hGrad hCe hEll hEll₁ hAlpha hv hSource
    mass M T diff phase hRate V G F
  let U (n : ℕ) (b : OrderedPair) := projectionFullSchwartz (z n) b.1 b.2
  let G₀ (n : ℕ) (b : OrderedPair) := projectedGaugeComplement (z n) b.1 b.2
  let W (n : ℕ) := actualWardPhaseSchwartz m wi wo hm hη i o (z n)
  let A (n : ℕ) := euclideanFieldGradientL3 (W n)
  let B (n : ℕ) := euclideanFieldGradientL3 (G₀ n) + euclideanFieldGradientL3 (V n)
  let error (n : ℕ) := ‖radianTrilinearForm F (G n) (V n l) (V n j)‖
  have hN (f : OrderedPair → SchwartzMap E ℂ) : 0 ≤ euclideanFieldGradientL3 f := ENNReal.toReal_nonneg
  have hE (n : ℕ) : error n ≤ (128 * C) * A n * (B n)^2 := by
    have h := (hForm wi wo hm η hη i o (z n)).2
    change error n ≤ C * wardCoordinateGradientL3 (G₀ n k) *
      (wardCoordinateGradientL3 (W n l) * wardCoordinateGradientL3 (V n j) +
        wardCoordinateGradientL3 (V n l) * wardCoordinateGradientL3 (W n j)) at h
    have hComp (f : OrderedPair → SchwartzMap E ℂ) (b : OrderedPair) := ward_coordinate_gradient_bound f b
    have hUpper : error n ≤ C * (4 * euclideanFieldGradientL3 (G₀ n)) *
        ((4 * A n) * (4 * euclideanFieldGradientL3 (V n)) +
          (4 * euclideanFieldGradientL3 (V n)) * (4 * A n)) := by
      refine h.trans ?_
      have hn (f : SchwartzMap E ℂ) : 0 ≤ wardCoordinateGradientL3 f :=
        Finset.sum_nonneg (fun _ _ => ENNReal.toReal_nonneg)
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hComp (G₀ n) k) hC)
        (add_le_add (mul_le_mul (hComp (W n) l) (hComp (V n) j) (hn _) (mul_nonneg (by norm_num) (hN _)))
          (mul_le_mul (hComp (V n) l) (hComp (W n) j) (hn _) (mul_nonneg (by norm_num) (hN _))))
        (add_nonneg (mul_nonneg (hn _) (hn _)) (mul_nonneg (hn _) (hn _)))
        (mul_nonneg hC (mul_nonneg (by norm_num) (hN _)))
    refine hUpper.trans ?_
    have hv₀ := hN (V n)
    have hg₀ := hN (G₀ n)
    have hp₀ : 0 ≤ A n := hN _
    have hB : euclideanFieldGradientL3 (G₀ n) * euclideanFieldGradientL3 (V n) ≤ (B n)^2 := by
      dsimp [B]
      nlinarith only [sq_nonneg (euclideanFieldGradientL3 (G₀ n)), sq_nonneg (euclideanFieldGradientL3 (V n)), mul_nonneg hv₀ hg₀]
    calc
      _ = (128 * C) * A n * (euclideanFieldGradientL3 (G₀ n) * euclideanFieldGradientL3 (V n)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB (mul_nonneg (mul_nonneg (by norm_num) hC) hp₀)
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
    filter_upwards [hBudget,hRate ε hε] with n hB hD
    have hThin := fieldGradientL3_sub_le (U n) (U n - V n)
    rw [sub_sub_cancel] at hThin
    have hd : euclideanFieldGradientL3 (U n - V n) ≤ Ce * ell ^ alpha * M + ε :=
      (actualThinSchwartz_cubicGradientDifference m wi wo hm hη i o (z n)).le.trans hD.1
    dsimp [B]
    linarith only [hThin, hd, hB.1, hB.2, hCeScale]
  have hTail := cubic_product_tail error A B (128 * C) (Ce * ell ^ alpha * M) ((128 * grad + Ce) * M)
    (by positivity) (mul_nonneg (mul_nonneg hCe (Real.rpow_nonneg hEll.le _)) hM₀)
    (fun n => add_nonneg (hN _) (hN _)) hE hA hB
  have hMass : M * M^2 = mass := by
    dsimp [M]
    rw [pow_two, ← Real.rpow_add_of_nonneg hm₀ (by norm_num : (0 : ℝ) ≤ 1 / 3)
      (by norm_num : (0 : ℝ) ≤ 1 / 3), ← Real.rpow_add_of_nonneg hm₀
        (by norm_num : (0 : ℝ) ≤ 1 / 3) (by norm_num : (0 : ℝ) ≤ 1 / 3 + 1 / 3)]
    rw [show (1 / 3 : ℝ) + (1 / 3 + 1 / 3) = 1 by norm_num, Real.rpow_one]
  have hScale : (128 * C) * (Ce * ell ^ alpha * M) * ((128 * grad + Ce) * M)^2 =
      (128 * C * Ce * (128 * grad + Ce)^2) * ell ^ alpha * mass := by
    rw [← hMass]
    ring
  simpa only [error, hScale] using hTail

end Burnett.C02
