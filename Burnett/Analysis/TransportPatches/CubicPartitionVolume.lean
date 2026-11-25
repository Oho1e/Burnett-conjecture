import Burnett.Analysis.TransportPatches.ScaledCubicPartition
import Mathlib.MeasureTheory.Integral.Lebesgue.Add

/-! Scale-independent overlap and the sum of the actual outer patch
volumes. Each patch is charged its own volume. -/
set_option autoImplicit false
set_option maxRecDepth 3600
set_option maxHeartbeats 2500000

noncomputable section

namespace Burnett.C01

open Set Metric MeasureTheory Burnett.Analysis.CarlesonEmbedding
open scoped ENNReal BigOperators

open private mem_patchBall_iff from Burnett.Analysis.TransportPatches.ScaledCubicPartition

/-- A point belongs to at most a fixed number of outer balls at any
positive scale. The finite selection of centers is arbitrary. -/
theorem scaled_patch_overlap (s : Finset LatticeIndex) (ℓ : ℝ) (hℓ : 0 < ℓ)
    (x : LatticeSpace) :
    letI := Classical.propDecidable
    (s.filter fun a => x ∈ closedBall (patchCenter ℓ a) (6 * ℓ)).card ≤ 17 ^ 4 := by
  classical
  let y : LatticeSpace := ℓ⁻¹ • x
  let b : LatticeIndex := fun j => Int.floor (y j)
  have hSub : (s.filter fun a => x ∈ closedBall (patchCenter ℓ a) (6 * ℓ)) ⊆
      s.filter fun a => latticeNear b a := by
    intro a ha
    obtain ⟨hAs, hAx⟩ := Finset.mem_filter.mp ha
    apply Finset.mem_filter.mpr
    refine ⟨hAs, latticeNear_symm (latticeNear_floor_of_dist_le_seven a y ?_)⟩
    rw [dist_comm, dist_eq_norm]
    exact ((mem_patchBall_iff ℓ hℓ a x 6).mp hAx).trans (by norm_num)
  exact (Finset.card_le_card hSub).trans (lattice_pair_degree s b)

/-- Summing the volume of the enlarged patches loses only the fixed
overlap multiplicity, independently of the scale and number of patches. -/
theorem sum_scaled_patch_measure_le (m : Measure LatticeSpace) (s : Finset LatticeIndex)
    (ℓ : ℝ) (hℓ : 0 < ℓ) (Kplus : Set LatticeSpace) (hK : MeasurableSet Kplus)
    (hPatches : ∀ a ∈ s, closedBall (patchCenter ℓ a) (6 * ℓ) ⊆ Kplus) :
    (∑ a ∈ s, m (closedBall (patchCenter ℓ a) (6 * ℓ))) ≤
      ((17 ^ 4 : ℕ) : ℝ≥0∞) * m Kplus := by
  classical
  let P (a : LatticeIndex) := closedBall (patchCenter ℓ a) (6 * ℓ)
  let v (a : LatticeIndex) := (P a).indicator (fun _ => (1 : ℝ≥0∞))
  let C : ℝ≥0∞ := ((17 ^ 4 : ℕ) : ℝ≥0∞)
  have hMeas (a : LatticeIndex) : Measurable (v a) :=
    measurable_const.indicator measurableSet_closedBall
  have hEq (a : LatticeIndex) : (∫⁻ x, v a x ∂m) = m (P a) := by
    dsimp [v]
    rw [lintegral_indicator_const measurableSet_closedBall, one_mul]
  have hPoint (x : LatticeSpace) : (∑ a ∈ s, v a x) ≤ Kplus.indicator (fun _ => C) x := by
    by_cases hx : x ∈ Kplus
    · rw [indicator_of_mem hx]
      calc
        _ = ∑ a ∈ s.filter (fun a => x ∈ P a), (1 : ℝ≥0∞) := by
          rw [Finset.sum_filter]
          simp [v, indicator_apply]
        _ = (((s.filter fun a => x ∈ P a).card : ℕ) : ℝ≥0∞) := by simp
        _ ≤ C := by
          dsimp [C]
          exact_mod_cast scaled_patch_overlap s ℓ hℓ x
    · rw [indicator_of_notMem hx]
      exact (Finset.sum_eq_zero fun a ha => indicator_of_notMem (fun hp =>
        hx (hPatches a ha hp)) _).le
  calc
    (∑ a ∈ s, m (P a)) = ∫⁻ x, (∑ a ∈ s, v a x) ∂m := by
      rw [lintegral_finset_sum s (fun a _ => hMeas a)]
      exact Finset.sum_congr rfl fun a _ => (hEq a).symm
    _ ≤ ∫⁻ x, Kplus.indicator (fun _ => C) x ∂m := lintegral_mono hPoint
    _ = C * m Kplus := lintegral_indicator_const hK C

end Burnett.C01
