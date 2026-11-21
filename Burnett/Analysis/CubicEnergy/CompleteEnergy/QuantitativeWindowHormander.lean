import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuantitativeWindowKernels
import Burnett.Analysis.SignedFourierWindow.HormanderBands
import Burnett.Analysis.SignedFourierWindow.CalderonFiniteKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open MeasureTheory Metric Finset

private theorem local_difference_bound (φ : SchwartzMap E ℂ) (A : ℝ)
    (h : ∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A) (b z : E) (hb : ‖b‖ ≤ 1) :
    ‖φ (z-b) - φ z‖ ≤ (32*A/(1+‖z‖)^5)*‖b‖ := by
  have deriv (w : E) (hw : w ∈ closedBall z 1) : ‖fderiv ℝ φ w‖ ≤ 32*A/(1+‖z‖)^5 := by
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

private theorem translation_L1_bound (φ : SchwartzMap E ℂ) (A : ℝ)
    (h : ∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A) (b : E) (hb : ‖b‖ ≤ 1) :
    (∫ z : E, ‖φ (z-b) - φ z‖) ≤ (32*A*(∫ z, kernelDecayWeight z))*‖b‖ := by
  have shift : Integrable (fun z : E => φ (z-b)) := by
    simpa only [sub_eq_add_neg] using
      ((measurePreserving_add_right (volume : Measure E) (-b)).integrable_comp_emb
        (Homeomorph.addRight (-b)).measurableEmbedding).2 φ.integrable
  have hi := (shift.sub φ.integrable).norm
  have bound (z : E) : ‖φ (z-b)-φ z‖ ≤ 32*A*‖b‖ * kernelDecayWeight z :=
    (local_difference_bound φ A h b z hb).trans_eq (by unfold kernelDecayWeight; ring)
  exact (integral_mono hi (integrable_kernelDecayWeight.const_mul _) bound).trans_eq
    (by rw [integral_const_mul]; ring)

private theorem unmodulated_difference_integral (φ : SchwartzMap E ℂ) (s : ℝ) (hs : 0<s) (h : E) :
    (∫ z : E, ‖shiftedSpatialKernel φ s 0 (z-h) - shiftedSpatialKernel φ s 0 z‖) =
      ∫ z : E, ‖φ (z - s⁻¹ • h) - φ z‖ := by
  let F := fun z : E => ‖φ (z - s⁻¹ • h) - φ z‖
  have H (z : E) : ‖shiftedSpatialKernel φ s 0 (z-h) - shiftedSpatialKernel φ s 0 z‖ =
      (s^4)⁻¹ * F (s⁻¹ • z) := by
    simp only [shiftedSpatialKernel,add_zero,F,← smul_sub,norm_smul,Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr (pow_pos hs _))]
  simp_rw [H]
  rw [integral_const_mul,Measure.integral_comp_inv_smul_of_nonneg volume F hs.le,
    show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin,smul_eq_mul,← mul_assoc,
    inv_mul_cancel₀ (pow_ne_zero _ hs.ne'),one_mul]

def annularHormanderBound (A : ℝ) : ℝ :=
  4 * (32*A*(∫ z, kernelDecayWeight z) + 2*A)

theorem annularHormanderBound_nonneg {A : ℝ} (hA : 0 ≤ A) : 0 ≤ annularHormanderBound A := by
  have hW : 0 ≤ ∫ z, kernelDecayWeight z := integral_nonneg kernelDecayWeight_nonneg
  unfold annularHormanderBound
  positivity

/-- A single spatial moment and the displayed derivative decay supply a common
Hörmander constant for every unmodulated finite dyadic frequency window. -/
theorem unmodulated_window_hormander (φ : SchwartzMap E ℂ) (A : ℝ) (hA : 0 ≤ A)
    (moment : (∫ z, ‖z‖ * ‖φ z‖) ≤ A)
    (deriv : ∀ z, (1+‖z‖)^5 * ‖fderiv ℝ φ z‖ ≤ A)
    (t : ℝ) (ht : 0 < t) (I : Finset ℕ) (h : E) :
    let K := finiteWindowKernel φ t 0 I (fun _ => 1)
    (∫ z in {z : E | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖) ≤ annularHormanderBound A := by
  intro K
  by_cases hz : h = 0
  · subst h
    simp only [sub_zero,sub_self,norm_zero,integral_zero]
    exact annularHormanderBound_nonneg hA
  have hd : 0 < ‖h‖ := norm_pos_iff.mpr hz
  let r := fun k : ℕ => (2:ℝ)^k*t
  let S := {z : E | 2*‖h‖ ≤ ‖z‖}
  let B := fun k => shiftedSpatialKernel φ (r k) 0
  let L := 32*A*(∫ z, kernelDecayWeight z)
  let D := L + 2*A
  have hW : 0 ≤ ∫ z, kernelDecayWeight z := integral_nonneg kernelDecayWeight_nonneg
  have hL : 0 ≤ L := by unfold L; positivity
  have hD : 0 ≤ D := by unfold D; positivity
  have dL : L ≤ D := le_add_of_nonneg_right (by positivity)
  have dM : 2*A ≤ D := le_add_of_nonneg_left hL
  have pos (k : ℕ) : 0 < r k := mul_pos (by positivity) ht
  have hB (k) : Integrable (B k) := shiftedSpatialKernel_integrable φ (pos k) 0
  let Δ := fun k (z : E) => B k (z-h) - B k z
  have diff (k) : Integrable (Δ k) := by
    have shift : Integrable (fun z : E => B k (z-h)) := by
      simpa only [sub_eq_add_neg] using
        ((measurePreserving_add_right (volume : Measure E) (-h)).integrable_comp_emb
          (Homeomorph.addRight (-h)).measurableEmbedding).2 (hB k)
    exact shift.sub (hB k)
  have one (k : ℕ) : (∫ z in S, ‖Δ k z‖) ≤ D*min (r k/‖h‖) (‖h‖/r k) := by
    by_cases hk : r k ≤ ‖h‖
    · rw [min_eq_left (((div_le_one hd).mpr hk).trans ((one_le_div (pos k)).mpr hk))]
      have small := exterior_difference_tail φ (r k) (pos k) 0 h hd
      simp only [norm_zero,zero_mul,add_zero] at small
      refine small.trans ?_
      rw [mul_right_comm (2:ℝ) (r k / ‖h‖)]
      exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left moment (by norm_num)).trans dM)
        (div_nonneg (pos k).le hd.le)
    · have hh := le_of_not_ge hk
      rw [min_eq_right (((div_le_one (pos k)).mpr hh).trans ((one_le_div hd).mpr hh))]
      have he : ‖(r k)⁻¹ • h‖ = ‖h‖ / r k := by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr (pos k).le),inv_mul_eq_div]
      have large : (∫ z, ‖Δ k z‖) ≤ L*(‖h‖/r k) := by
        change (∫ z, ‖shiftedSpatialKernel φ (r k) 0 (z-h) - shiftedSpatialKernel φ (r k) 0 z‖) ≤ _
        rw [unmodulated_difference_integral φ (r k) (pos k) h, ← he]
        exact translation_L1_bound φ A deriv _ (he.trans_le ((div_le_one (pos k)).mpr hh))
      exact (setIntegral_le_integral (diff k).norm (Filter.Eventually.of_forall fun _ => norm_nonneg _)).trans
        (large.trans (mul_le_mul_of_nonneg_right dL (div_nonneg hd.le (pos k).le)))
  change (∫ z in S, ‖(∑ k ∈ I, 1 * B k (z-h)) - (∑ k ∈ I, 1 * B k z)‖) ≤ _
  simp only [one_mul]
  simp_rw [← sum_sub_distrib]
  change (∫ z in S, ‖∑ k ∈ I, Δ k z‖) ≤ _
  calc
    _ ≤ ∫ z in S, ∑ k ∈ I, ‖Δ k z‖ :=
      integral_mono (integrable_finset_sum I (fun k _ => diff k)).norm.integrableOn
        (integrable_finset_sum I (fun k _ => (diff k).norm)).integrableOn (fun z => norm_sum_le _ _)
    _ = ∑ k ∈ I, ∫ z in S, ‖Δ k z‖ := integral_finset_sum _ (fun k _ => (diff k).norm.integrableOn)
    _ ≤ ∑ k ∈ I, D*min (r k/‖h‖) (‖h‖/r k) := sum_le_sum fun k _ => one k
    _ ≤ D*4 := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (dyadic_difference_sum I t ‖h‖ ht hd) hD
    _ = _ := by unfold D L annularHormanderBound; ring

end Burnett.A02.FrequencySplit
