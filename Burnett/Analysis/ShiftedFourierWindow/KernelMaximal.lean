import Burnett.Analysis.CenteredMaximal.MaximalLp

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.ShiftedFourierWindow

open Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric Set
open scoped ENNReal

theorem ball_mass_le_centeredMax (g : Space → ℝ≥0∞) (x : Space) {r : ℝ} (hr : 0 < r) :
    (∫⁻ y in closedBall x r, g y) ≤ volume (closedBall x r) * centeredMax g x :=
  (ENNReal.div_le_iff' (measure_closedBall_pos volume x hr).ne' measure_closedBall_lt_top.ne).mp
    (le_iSup (fun t : {t : ℝ // 0 < t} => (∫⁻ y in closedBall x t, g y) / volume (closedBall x t)) ⟨r,hr⟩)

/-- An integrable sum of centered ball majorants controls the absolute spatial
kernel integral by the full centered maximal function. -/
theorem kernel_le_centeredMax (g K : Space → ℝ≥0∞) (hg : Measurable g) (x : Space)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n) (a : ℕ → ℝ≥0∞)
    (hK : ∀ y, K y ≤ ∑' n, (closedBall x (r n)).indicator (fun _ => a n) y) :
    (∫⁻ y, K y * g y) ≤ (∑' n, a n * volume (closedBall x (r n))) * centeredMax g x := by
  let F := fun n : ℕ => (closedBall x (r n)).indicator (fun y => a n * g y)
  have hm (n : ℕ) : Measurable (F n) := (measurable_const.mul hg).indicator measurableSet_closedBall
  calc
    _ ≤ ∫⁻ y, ∑' n, F n y := by
      refine lintegral_mono (fun y => ?_)
      calc
        _ ≤ (∑' n, (closedBall x (r n)).indicator (fun _ => a n) y) * g y :=
          mul_le_mul_right' (hK y) _
        _ = _ := by simp only [F, Set.indicator_mul_left, ENNReal.tsum_mul_right]
    _ = ∑' n, ∫⁻ y, F n y := lintegral_tsum (fun n => (hm n).aemeasurable)
    _ ≤ ∑' n, (a n * volume (closedBall x (r n))) * centeredMax g x := by
      apply ENNReal.tsum_le_tsum
      intro n
      rw [show (∫⁻ y, F n y) = a n * ∫⁻ y in closedBall x (r n), g y from by
        simp only [F, lintegral_indicator measurableSet_closedBall, lintegral_const_mul _ hg]]
      rw [mul_assoc]
      exact mul_le_mul_left' (ball_mass_le_centeredMax g x (hr n)) _
    _ = _ := ENNReal.tsum_mul_right

end Burnett.Analysis.ShiftedFourierWindow
