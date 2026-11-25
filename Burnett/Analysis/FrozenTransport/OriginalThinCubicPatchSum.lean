import Burnett.Analysis.FrozenTransport.OriginalThinCubicFamily
import Burnett.Analysis.TransportPatches.CubicPartitionVolume

set_option autoImplicit false
set_option maxRecDepth 4000
set_option maxHeartbeats 5200000
noncomputable section

namespace Burnett.C02

open Set Filter MeasureTheory Metric
open Burnett.A02.FrequencySplit Burnett.RicciSymbol
open Burnett.C01 (patchCenter sum_scaled_patch_measure_le)
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open Burnett.Analysis.CarlesonEmbedding (LatticeIndex)
open scoped BigOperators ENNReal Topology

/-- A common error coefficient for the actual complete cubic replacement on
each patch sums over the C01 lattice using its fixed overlap constant. The
(n)-tail is taken jointly for the finite family at the fixed (\ell). -/
theorem completeCubic_thinReplacement_sum_scaled_patch
    (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (K : Set E) (hK : IsCompact K)
    (hPatch : ∀ j ∈ s, closedBall (patchCenter ℓ j) (6 * ℓ) ⊆ K)
    (c : LatticeIndex → EnergyIndex OrderedPair → OrderedPair → ℝ)
    (q : LatticeIndex → Index → Index → OrderedPair → OrderedPair → OrderedPair → ℝ)
    (b : LatticeIndex → E → ℝ) (cut add : SchwartzMap E ℂ)
    (u v G : LatticeIndex → ℕ → RealEnergyField OrderedPair) (C alpha : ℝ) (hC : 0 ≤ C)
    (hRate : ∀ j ∈ s, ∀ ε > 0, ∀ᶠ n in atTop,
      |completeCubicEnergy (c j) (q j) (fixedInfraredSymbol cut add (b j)) (u j n + G j n) -
        completeCubicEnergy (c j) (q j) (fixedInfraredSymbol cut add (b j)) (v j n + G j n)| ≤
        C * ℓ ^ alpha * ((volume : Measure E) (closedBall (patchCenter ℓ j) (6 * ℓ))).toReal + ε) :
    ∀ ε > 0, ∀ᶠ n in atTop,
      |(∑ j ∈ s, completeCubicEnergy (c j) (q j) (fixedInfraredSymbol cut add (b j)) (u j n + G j n)) -
        (∑ j ∈ s, completeCubicEnergy (c j) (q j) (fixedInfraredSymbol cut add (b j)) (v j n + G j n))| ≤
        (17 ^ 4 : ℝ) * C * ℓ ^ alpha * ((volume : Measure E) K).toReal + ε := by
  intro ε hε
  let P (j : LatticeIndex) : Set E := closedBall (patchCenter ℓ j) (6 * ℓ)
  let w (j : LatticeIndex) := ((volume : Measure E) (P j)).toReal
  let U (j : LatticeIndex) (n : ℕ) := completeCubicEnergy (c j) (q j) (fixedInfraredSymbol cut add (b j)) (u j n + G j n)
  let V (j : LatticeIndex) (n : ℕ) := completeCubicEnergy (c j) (q j) (fixedInfraredSymbol cut add (b j)) (v j n + G j n)
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
  have hAll : ∀ᶠ n in atTop, ∀ j ∈ s, |U j n - V j n| ≤ C * ℓ ^ alpha * w j + t :=
    (s.eventually_all).2 (fun j hj => hRate j hj t ht)
  filter_upwards [hAll] with n hn
  change |(∑ j ∈ s, U j n) - (∑ j ∈ s, V j n)| ≤ _
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ j ∈ s, |U j n - V j n| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ s, (C * ℓ ^ alpha * w j + t) := Finset.sum_le_sum hn
    _ = C * ℓ ^ alpha * ∑ j ∈ s, w j + (s.card : ℝ) * t := by
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    _ ≤ C * ℓ ^ alpha * ((17 ^ 4 : ℝ) * ((volume : Measure E) K).toReal) + ε := by
      have hNonneg : 0 ≤ C * ℓ ^ alpha := mul_nonneg hC (Real.rpow_nonneg hℓ.le _)
      exact add_le_add (mul_le_mul_of_nonneg_left hVolumes hNonneg) hCount
    _ = _ := by ring

end Burnett.C02
