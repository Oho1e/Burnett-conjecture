import Burnett.Analysis.SignedFourierWindow.SignLowerMoment

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.DyadicSquare hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Finset MeasureTheory
open scoped ENNReal

def signAverageEnn : (n : ℕ) → ((Fin n → Bool) → ℝ≥0∞) → ℝ≥0∞
  | 0, F => F Fin.elim0
  | n+1, F => (2:ℝ≥0∞)⁻¹*(signAverageEnn n (fun s => F (Fin.cons false s)) +
      signAverageEnn n (fun s => F (Fin.cons true s)))

private theorem ofReal_average {n : ℕ} (F : (Fin n → Bool) → ℝ) (hn : ∀ s, 0≤F s) :
    ENNReal.ofReal (signAverage n F) = signAverageEnn n (fun s => ENNReal.ofReal (F s)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have nn (b : Bool) : 0≤ signAverage n (fun s => F (Fin.cons b s)) :=
      (signAverage_const n 0).symm.trans_le (signAverage_mono (fun s => hn _))
    simp only [signAverage,signAverageEnn,div_eq_inv_mul,ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤2⁻¹),
      ENNReal.ofReal_add (nn false) (nn true),ih _ (fun _ => hn _)]
    rw [ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2),ENNReal.ofReal_ofNat]

private theorem average_le {n : ℕ} (F : (Fin n → Bool) → ℝ≥0∞) (M : ℝ≥0∞) (h : ∀ s, F s ≤ M) :
    signAverageEnn n F ≤ M := by
  induction n with
  | zero => exact h _
  | succ n ih =>
    refine (mul_le_mul_left' (add_le_add (ih _ (fun s => h (Fin.cons false s))) (ih _ (fun s => h (Fin.cons true s)))) _).trans_eq ?_
    rw [← two_mul,← mul_assoc,ENNReal.inv_mul_cancel (by norm_num) (by norm_num),one_mul]

private theorem measurable_average {n : ℕ} (F : (Fin n → Bool) → Space → ℝ≥0∞) (h : ∀ s, Measurable (F s)) :
    Measurable (fun x => signAverageEnn n (fun s => F s x)) := by
  induction n with
  | zero => exact h _
  | succ n ih => exact measurable_const.mul ((ih _ (fun s => h (Fin.cons false s))).add (ih _ (fun s => h (Fin.cons true s))))

theorem integral_signAverage {n : ℕ} (F : (Fin n → Bool) → Space → ℝ≥0∞) (h : ∀ s, Measurable (F s)) :
    (∫⁻ x, signAverageEnn n (fun s => F s x)) = signAverageEnn n (fun s => ∫⁻ x, F s x) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [signAverageEnn]
    rw [lintegral_const_mul' _ _ (by norm_num),lintegral_add_left (measurable_average _ (fun s => h (Fin.cons false s))),
      ih _ (fun s => h (Fin.cons false s)),ih _ (fun s => h (Fin.cons true s))]

/-- Uniform bounds on signed sums control the spatial square function of the
same finite family. Sign words are fixed across the entire integral. -/
theorem square_integral_from_signs {n : ℕ} (v : Fin n → Space → ℂ) (hm : ∀ i, Measurable (v i)) (p : ℝ)
    (hp : 0<p) (M : ℝ≥0∞)
    (bound : ∀ s : Fin n → Bool, (∫⁻ x, ‖signedVector (fun i => v i x) s‖ₑ^p) ≤ M) :
    (∫⁻ x, ENNReal.ofReal ((Real.sqrt (vectorEnergy (fun i => v i x)))^p)) ≤
      ENNReal.ofReal (24*2^p) * M := by
  let F := fun (s : Fin n → Bool) (x : Space) => ‖signedVector (fun i => v i x) s‖ₑ^p
  have mf (s : Fin n → Bool) : Measurable (F s) := by
    have sum : Measurable (fun x => signedVector (fun i => v i x) s) := by
      unfold signedVector
      exact Finset.measurable_sum _ (fun i _ => measurable_const.mul (hm i))
    exact sum.enorm.pow_const p
  have point (x : Space) : ENNReal.ofReal ((Real.sqrt (vectorEnergy (fun i => v i x)))^p) ≤
      ENNReal.ofReal (24*2^p) * signAverageEnn n (fun s => F s x) := by
    have h := ENNReal.ofReal_le_ofReal (square_le_sign_moment (fun i => v i x) p hp)
    rw [ENNReal.ofReal_mul (by positivity),ofReal_average _ (fun s => Real.rpow_nonneg (norm_nonneg _) p)] at h
    simpa only [F,← ofReal_norm_eq_enorm,ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le] using h
  apply (lintegral_mono point).trans
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,integral_signAverage F mf]
  exact mul_le_mul_left' (average_le _ M bound) _

end Burnett.Analysis.SignedFourierWindow
