import Burnett.Analysis.SignedFourierWindow.CalderonPartition

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set Function
open scoped ENNReal

/-- The exceptional region is large enough to use the integral Hörmander
condition against each bad block supported on the fourfold ball. -/
theorem eightfold_exceptional_volume {u : Set Space} (hu : u.Countable) (r : Space → ℝ) (hr : ∀ i : u, 0<r i)
    (Q : u → Set Space) (disj : Pairwise (Disjoint on Q)) (sub : ∀ i : u, closedBall (i:Space) (r i) ⊆ Q i)
    (g : Space → ℝ≥0∞) (a : ℝ≥0∞)
    (lower : ∀ i : u, a * volume (closedBall (i:Space) (r i)) < ∫⁻ y in closedBall (i:Space) (r i), g y) :
    a*volume (⋃ i : u, closedBall (i:Space) (8*r i)) ≤ 4096*∫⁻ y,g y := by
  letI : Countable u := hu.to_subtype
  let B := fun i : u => closedBall (i:Space) (r i)
  let V := fun i : u => closedBall (i:Space) (8*r i)
  have hV (i : u) : volume (V i) = 4096*volume (B i) := by
    dsimp only [V,B]
    rw [Measure.addHaar_closedBall_mul volume (i:Space) (by norm_num : (0:ℝ) ≤ 8) (hr i).le,
      Measure.addHaar_closedBall_center volume (i:Space)]
    norm_num [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]
  have hd : Pairwise (Disjoint on B) := fun i j h => (disj h).mono (sub i) (sub j)
  calc
    _ ≤ a * ∑' i : u, volume (V i) := mul_le_mul_left' (measure_iUnion_le V) _
    _ = 4096 * ∑' i : u, a * volume (B i) := by simp_rw [hV,ENNReal.tsum_mul_left]; ac_rfl
    _ ≤ 4096 * ∑' i : u, ∫⁻ y in B i,g y := mul_le_mul_left' (ENNReal.tsum_le_tsum (fun i => (lower i).le)) _
    _ ≤ _ := by
      rw [← lintegral_iUnion (fun _ => measurableSet_closedBall) hd g]
      exact mul_le_mul_left' (setLIntegral_le_lintegral _ _) _

end Burnett.Analysis.SignedFourierWindow
