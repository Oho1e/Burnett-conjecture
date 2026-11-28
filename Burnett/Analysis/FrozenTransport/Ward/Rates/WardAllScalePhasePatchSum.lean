import Burnett.Analysis.TransportPatches.CubicPartitionVolume
import Burnett.Analysis.FrozenTransport.Ward.Rates.WardAllScalePhysicalPhaseRecombination

set_option autoImplicit false
set_option maxRecDepth 6600
set_option maxHeartbeats 5200000

noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Metric Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open Burnett.C01 (patchCenter sum_scaled_patch_measure_le)
open scoped ENNReal

/-- The compact-uniform physical-phase error on each original cube
sums with the actual bounded overlap of the C03 patch balls. -/
theorem wardPhysicalPhase_sum_scaled_patch
    (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (K : Set E) (hK : IsCompact K) (hPatch : ∀ j ∈ s, closedBall (patchCenter ℓ j) (6 * ℓ) ⊆ K)
    (F : LatticeIndex → ℕ → ℂ) (C α : ℝ) (hC : 0 ≤ C)
    (hRate : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop,
      ‖F j n‖ ≤ C * ℓ ^ α * ((volume : Measure E) (closedBall (patchCenter ℓ j) (6 * ℓ))).toReal + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      (∑ j ∈ s, ‖F j n‖) ≤ (17 ^ 4 : ℝ) * C * ℓ ^ α * ((volume : Measure E) K).toReal + ε := by
  intro ε hε
  let P (j : LatticeIndex) := closedBall (patchCenter ℓ j) (6 * ℓ)
  let w (j : LatticeIndex) := ((volume : Measure E) (P j)).toReal
  let t : ℝ := ε / (s.card + 1)
  have hDen : 0 < (s.card : ℝ) + 1 := by positivity
  have ht : 0 < t := div_pos hε hDen
  have hCount : (s.card : ℝ) * t ≤ ε := by
    dsimp only [t]
    rw [← mul_div_assoc, div_le_iff₀ hDen]
    linarith
  have hFinite (j : LatticeIndex) : (volume : Measure E) (P j) ≠ ⊤ :=
    (isCompact_closedBall _ _).measure_lt_top.ne
  have hVolumes : (∑ j ∈ s, w j) ≤ (17 ^ 4 : ℝ) * ((volume : Measure E) K).toReal := by
    have hSum := sum_scaled_patch_measure_le volume s ℓ hℓ K hK.measurableSet hPatch
    have hRight : (((17 ^ 4 : ℕ) : ℝ≥0∞) * (volume : Measure E) K) ≠ ⊤ :=
      (ENNReal.mul_lt_top (by norm_num) hK.measure_lt_top).ne
    have h := ENNReal.toReal_mono hRight hSum
    rw [ENNReal.toReal_sum (fun j _ => hFinite j), ENNReal.toReal_mul] at h
    exact_mod_cast h
  have hAll : ∀ᶠ n in atTop, ∀ j ∈ s, ‖F j n‖ ≤ C * ℓ ^ α * w j + t :=
    (s.eventually_all).2 (fun j hj => hRate j hj t ht)
  filter_upwards [hAll] with n hn
  calc
    _ ≤ ∑ j ∈ s, (C * ℓ ^ α * w j + t) := Finset.sum_le_sum hn
    _ = C * ℓ ^ α * (∑ j ∈ s, w j) + (s.card : ℝ) * t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * ℓ ^ α * ((17 ^ 4 : ℝ) * ((volume : Measure E) K).toReal) + ε := by
      exact add_le_add (mul_le_mul_of_nonneg_left hVolumes (mul_nonneg hC (Real.rpow_nonneg hℓ.le _))) hCount
    _ = _ := by ring

end Burnett.C02
