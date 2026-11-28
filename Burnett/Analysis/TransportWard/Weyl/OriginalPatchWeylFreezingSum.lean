import Burnett.Analysis.TransportWard.Weyl.OriginalPatchFreezingVolume

set_option autoImplicit false
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.V03

open Filter Metric MeasureTheory Set Burnett.A02.FrequencySplit Burnett.RicciSymbol Burnett.P01
open Burnett.Geometry.ConnectionDifference
open Burnett.A02.FieldAndCoefficientReview (fieldValueArray)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter)
open scoped BigOperators ENNReal Topology ContDiff

/-- The same ordered C03 input has the support of its original spatial
cutoff before either the physical or the gauge multiplier is applied. -/
theorem fieldValueArray_tsupport_of_original_raw_patch
    (z : ProjectionSchwartzMatrix) (χ : E → ℝ) (g g₀ : E → Tensor2)
    (hz : ∀ i j x, z i j x = ((χ x * (g x i j - g₀ x i j) : ℝ) : ℂ)) :
    tsupport (fieldValueArray (fun k : OrderedPair => z k.1 k.2)) ⊆ tsupport χ := by
  apply closure_minimal ?_ isClosed_closure
  intro x hx
  by_contra hχ
  apply hx
  apply PiLp.ext
  intro k
  change z k.1 k.2 x = 0
  rw [hz, image_eq_zero_of_notMem_tsupport hχ, zero_mul, Complex.ofReal_zero]

/-- Carry the physical freezing estimate through the exact raw C03 family.
The derivative scale on the cutoff cancels against the metric convergence
on the fixed-scale tail, leaving a scale-independent volume coefficient. -/
theorem eventually_sum_originalRawPatch_freezing_C03
    (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (hPatch : ∀ j ∈ s, closedBall (patchCenter ℓ j) (6 * ℓ) ⊆ K)
    (g : ℕ → E → Tensor2) (g₀ : E → Tensor2)
    (hg : ∀ n i j, ContDiffOn ℝ ∞ (fun x => g n x i j) U)
    (hg₀ : ∀ i j, ContDiffOn ℝ ∞ (fun x => g₀ x i j) U)
    (e : ℕ → ℝ) (he₀ : ∀ n, 0 ≤ e n) (he : Tendsto e atTop (𝓝 0))
    (C L D : ℝ) (hC : 0 ≤ C) (hL : 0 ≤ L) (hD : 0 ≤ D)
    (hField : ∀ n x, x ∈ K → ‖g n x - g₀ x‖ ≤ e n ∧
      ‖coordinateJet (g n) x - coordinateJet g₀ x‖ ≤ D)
    (χ : LatticeIndex → E → ℝ)
    (hχ : ∀ j ∈ s, ContDiff ℝ ∞ (χ j) ∧ tsupport (χ j) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) ∧
      ∀ x ∈ tsupport (χ j), ‖χ j x‖ ≤ C ∧ ‖iteratedFDeriv ℝ 1 (χ j) x‖ ≤ L * ℓ⁻¹)
    (z : LatticeIndex → ℕ → ProjectionSchwartzMatrix)
    (hz : ∀ᶠ n in atTop, ∀ j ∈ s, ∀ i k x,
      z j n i k x = ((χ j x * (g n x i k - g₀ x i k) : ℝ) : ℂ))
    (err : ℕ → LatticeIndex → ℝ) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hEstimate : ∀ j ∈ s, ∀ n,
      let u (k : OrderedPair) := z j n k.1 k.2
      tsupport (fieldValueArray u) ⊆ closedBall (patchCenter ℓ j) (4 * ℓ) →
      |err n j| ≤ A * ℓ * euclideanFieldGradientL3 u ^ 3 +
        B * euclideanFieldValueL3 u * euclideanFieldGradientL3 u ^ 2) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∑ j ∈ s, |err n j|) ≤
        (17 ^ 4 : ℝ) * (A * (64 * (C * D + L)) ^ 3) * ℓ * ((volume : Measure E) K).toReal + ε := by
  have hGrad : 0 ≤ 64 * (C * D + L) := by positivity
  apply eventually_sum_cubic_freezing_errors_le_patch_volumes s ℓ hℓ K hK hPatch err _ (by positivity)
  intro j hj
  let W := closedBall (patchCenter ℓ j) (6 * ℓ)
  let u (n : ℕ) (k : OrderedPair) := z j n k.1 k.2
  let V := ((volume : Measure E) W).toReal ^ (1 / 3 : ℝ)
  obtain ⟨hχs, hInner, hCut⟩ := hχ j hj
  have hχc : HasCompactSupport (χ j) := (isCompact_closedBall _ _).of_isClosed_subset isClosed_closure hInner
  have hχW : tsupport (χ j) ⊆ W := hInner.trans (closedBall_subset_closedBall (by linarith))
  have hBudget : ∀ᶠ n in atTop, euclideanFieldValueL3 (u n) ≤ 16 * (C * e n) * V ∧
      euclideanFieldGradientL3 (u n) ≤ 64 * (C * D + L * ℓ⁻¹ * e n) * V := by
    filter_upwards [hz] with n hn
    exact originalRawPatch_euclideanLp_of_C03 hU (isCompact_closedBall _ _) ((hPatch j hj).trans hKU)
      (g n) g₀ (hg n) hg₀ (χ j) hχs hχc hχW (z j n) (hn j hj) C (L * ℓ⁻¹) D (e n)
      hC (mul_nonneg hL (inv_nonneg.mpr hℓ.le)) hD (he₀ n)
      (fun x hx => (hCut x hx).1) (fun x hx => (hCut x hx).2)
      (fun x hx => hField n x (hPatch j hj (hχW hx)))
  have hSmall : Tendsto (fun n => 16 * (C * e n) * V) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_mul] using (((he.const_mul C).const_mul (16 : ℝ)).mul_const V)
  have hY := squeeze_zero' (Eventually.of_forall fun n => show 0 ≤ euclideanFieldValueL3 (u n) from ENNReal.toReal_nonneg)
    (hBudget.mono fun _ h => h.1) hSmall
  have hX : ∀ᶠ n in atTop, euclideanFieldGradientL3 (u n) ≤ (64 * (C * D + L)) * V := by
    filter_upwards [hBudget, (tendsto_order.1 he).2 ℓ hℓ] with n hn heℓ
    have he' : L * ℓ⁻¹ * e n ≤ L := calc
      _ ≤ L * ℓ⁻¹ * ℓ := mul_le_mul_of_nonneg_left heℓ.le (mul_nonneg hL (inv_nonneg.mpr hℓ.le))
      _ = L := by rw [mul_assoc, inv_mul_cancel₀ hℓ.ne', mul_one]
    exact hn.2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (add_le_add_left he' _) (by norm_num))
      (Real.rpow_nonneg ENNReal.toReal_nonneg _))
  have hE : ∀ᶠ n in atTop,
      |err n j| ≤ A * ℓ * euclideanFieldGradientL3 (u n) ^ 3 +
        B * euclideanFieldValueL3 (u n) * euclideanFieldGradientL3 (u n) ^ 2 := by
    filter_upwards [hz] with n hn
    exact hEstimate j hj n ((fieldValueArray_tsupport_of_original_raw_patch (z j n) (χ j) (g n) g₀
      (hn j hj)).trans hInner)
  exact eventual_cubic_freezing_error_le_patch_volume u (fun n => err n j) W ℓ A B
    (64 * (C * D + L)) hℓ hA hB hY hX hE

end Burnett.V03
