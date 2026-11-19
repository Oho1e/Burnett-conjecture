import Burnett.Analysis.SignedFourierWindow.ShiftedTail
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open MeasureTheory Metric

private theorem derivative_decay (φ : SchwartzMap Space ℂ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A := by
  let ψ := SchwartzMap.fderivCLM ℝ φ
  let m : ℕ × ℕ := (5,0)
  let A := (2:ℝ)^5 * (Finset.Iic m).sup (fun i => SchwartzMap.seminorm ℝ i.1 i.2) ψ
  have hd (z : Space) : (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A := by
    simpa [A,m,ψ,SchwartzMap.fderivCLM_apply] using SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (5,0)) (k := 5) (n := 0) le_rfl le_rfl ψ z
  exact ⟨A,(norm_nonneg _).trans (by simpa using hd 0),hd⟩

private theorem local_difference (φ : SchwartzMap Space ℂ) (A : ℝ)
    (h : ∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A) (b z : Space) (hb : ‖b‖ ≤ 1) :
    ‖φ (z-b) - φ z‖ ≤ (32*A/(1+‖z‖)^5)*‖b‖ := by
  have deriv (w : Space) (hw : w ∈ closedBall z 1) : ‖fderiv ℝ φ w‖ ≤ 32*A/(1+‖z‖)^5 := by
    have hw' : ‖w-z‖ ≤ 1 := by simpa only [mem_closedBall,dist_eq_norm] using hw
    have hn : ‖z‖ ≤ ‖w‖ + ‖w-z‖ := by simpa using norm_sub_le w (w-z)
    have growth : 1+‖z‖ ≤ 2*(1+‖w‖) := by linarith [norm_nonneg w]
    apply (le_div_iff₀ (by positivity)).mpr
    calc
      _ ≤ ‖fderiv ℝ φ w‖ * (2*(1+‖w‖))^5 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) growth _) (norm_nonneg _)
      _ = 32*((1+‖w‖)^5 * ‖fderiv ℝ φ w‖) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (h w) (by norm_num)
  have point : z-b ∈ closedBall z 1 := by simpa [mem_closedBall,dist_eq_norm] using hb
  have H := (convex_closedBall z 1).norm_image_sub_le_of_norm_fderiv_le
    (fun w _ => (φ.differentiable w)) deriv (mem_closedBall_self (by norm_num : (0:ℝ)≤1)) point
  simpa using H

theorem schwartz_translation_L1 (φ : SchwartzMap Space ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Space, ‖b‖ ≤ 1 →
      (∫ z : Space, ‖φ (z-b) - φ z‖) ≤ C*‖b‖ := by
  obtain ⟨A,hA,hd⟩ := derivative_decay φ
  let w := fun z : Space => ((1+‖z‖)^5)⁻¹
  have hw : Integrable w := by
    have sq : (Module.finrank ℝ Space : ℝ) < (5:ℝ) := by rw [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]; norm_num
    have hi := integrable_one_add_norm (μ := (volume : Measure Space)) sq
    convert hi using 1
    ext z
    simp [w,Real.rpow_neg (by positivity : 0 ≤ 1+‖z‖)]
  have hpos : 0 ≤ ∫ z, w z := integral_nonneg fun z => by dsimp [w]; positivity
  refine ⟨32*A*(∫ z,w z),by positivity,?_⟩
  intro b hb
  have shift : Integrable (fun z : Space => φ (z-b)) := by
    simpa only [sub_eq_add_neg] using
      ((measurePreserving_add_right (volume : Measure Space) (-b)).integrable_comp_emb
        (Homeomorph.addRight (-b)).measurableEmbedding).2 φ.integrable
  have hi := (shift.sub φ.integrable).norm
  have bound (z : Space) : ‖φ (z-b)-φ z‖ ≤ 32*A*‖b‖ * w z := by
    exact (local_difference φ A hd b z hb).trans_eq (by dsimp [w]; ring)
  have hbnd := integral_mono hi (hw.const_mul (32*A*‖b‖)) bound
  exact hbnd.trans_eq (by rw [integral_const_mul]; ring)

end Burnett.Analysis.SignedFourierWindow
