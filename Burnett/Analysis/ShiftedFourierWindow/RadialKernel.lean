import Burnett.Analysis.ShiftedFourierWindow.KernelMaximal

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.ShiftedFourierWindow

open Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric Set
open scoped ENNReal

private theorem decay_ball_majorant (K : Space → ℝ) (hK : ∀ y, 0 ≤ K y) (x : Space)
    (s : ℝ) (hs : 0 < s) (A : ℝ) (hA : 0 ≤ A)
    (decay : ∀ y, (1 + dist y x / s)^5 * K y ≤ A) (y : Space) :
    ENNReal.ofReal (K y) ≤ ∑' n : ℕ, (closedBall x ((2:ℝ)^n*(2*s))).indicator
      (fun _ => ENNReal.ofReal A * ENNReal.ofReal (1/32:ℝ)^n) y := by
  have hd : 0 ≤ dist y x / s := div_nonneg dist_nonneg hs.le
  obtain ⟨n,hl,hu⟩ := exists_nat_pow_near (show 1 ≤ 1 + dist y x / s by linarith) (by norm_num : (1:ℝ)<2)
  have hmem : y ∈ closedBall x ((2:ℝ)^n*(2*s)) := by
    rw [mem_closedBall]
    rw [pow_succ] at hu
    have hlt : dist y x / s ≤ (2:ℝ)^n*2 := by linarith
    simpa only [mul_assoc] using (div_le_iff₀ hs).mp hlt
  have hpow : ((2:ℝ)^n)^5 = (32:ℝ)^n := by rw [pow_right_comm]; norm_num
  have hle := (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hl 5) (hK y)).trans (decay y)
  rw [hpow,mul_comm] at hle
  have hreal : K y ≤ A * (1 / 32 : ℝ)^n := by
    rw [one_div_pow,mul_one_div]
    exact (le_div_iff₀ (by positivity)).mpr hle
  apply le_trans _ (ENNReal.le_tsum n)
  rw [indicator_of_mem hmem, ← ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 1/32),
    ← ENNReal.ofReal_mul hA]
  exact ENNReal.ofReal_le_ofReal hreal

/-- In dimension four a fifth power of radial decay suffices for a uniform
centered maximal bound; the closed-ball volume here scales like s⁴. -/
theorem polynomial_kernel_maximal (g : Space → ℝ≥0∞) (hg : Measurable g)
    (K : Space → ℝ) (hK : ∀ y, 0 ≤ K y) (x : Space) (s : ℝ) (hs : 0 < s) (A : ℝ) (hA : 0 ≤ A)
    (decay : ∀ y, (1 + dist y x / s)^5 * K y ≤ A) :
    (∫⁻ y, ENNReal.ofReal (K y) * g y) ≤
      (ENNReal.ofReal A * volume (closedBall (0:Space) (2*s)) * 2) * centeredMax g x := by
  have mass (n : ℕ) : volume (closedBall x ((2:ℝ)^n*(2*s))) =
      ENNReal.ofReal (16:ℝ)^n * volume (closedBall (0:Space) (2*s)) := by
    rw [Measure.addHaar_closedBall_mul_of_pos volume x (by positivity),
        show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin, pow_right_comm]
    norm_num [ENNReal.ofReal_pow]
  have h := kernel_le_centeredMax g (fun y => ENNReal.ofReal (K y)) hg x
      (fun n => (2:ℝ)^n*(2*s)) (fun _ => by positivity)
      (fun n => ENNReal.ofReal A * ENNReal.ofReal (1/32:ℝ)^n) (decay_ball_majorant K hK x s hs A hA decay)
  apply h.trans_eq
  congr 1
  let V := volume (closedBall (0:Space) (2*s))
  have geom (n : ℕ) :
      (ENNReal.ofReal A * ENNReal.ofReal (1/32:ℝ)^n) * volume (closedBall x ((2:ℝ)^n*(2*s))) =
      (ENNReal.ofReal A * V) * (2⁻¹ : ℝ≥0∞)^n := by
    rw [mass]
    change _ * (_ * V) = _
    have hnum : ENNReal.ofReal (1/32:ℝ) * ENNReal.ofReal (16:ℝ) = (2:ℝ≥0∞)⁻¹ := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      norm_num
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]
      norm_num [one_div]
    rw [← hnum,mul_pow]
    ac_rfl
  simp_rw [geom]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_two]

end Burnett.Analysis.ShiftedFourierWindow
