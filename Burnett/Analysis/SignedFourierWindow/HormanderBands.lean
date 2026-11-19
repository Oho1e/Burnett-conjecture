import Burnett.Analysis.SignedFourierWindow.PhysicalDifferences
import Burnett.Analysis.SignedFourierWindow.DyadicDifferences

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal
open MeasureTheory Finset
open scoped BigOperators

/-- The integral Hörmander condition for finite dyadic sums of translated
Schwartz kernels, uniform in all coefficients of modulus at most one. -/
theorem dyadic_kernel_hormander (φ : SchwartzMap Space ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0<t → ∀ (q h : Space) (I : Finset ℕ) (c : ℕ → ℂ), (∀ k, ‖c k‖ ≤ 1) →
      (∫ z in {z : Space | 2*‖h‖ ≤ ‖z‖},
        ‖(∑ k ∈ I, c k * shiftedSpatialKernel φ ((2:ℝ)^k*t) q (z-h)) -
          (∑ k ∈ I, c k * shiftedSpatialKernel φ ((2:ℝ)^k*t) q z)‖) ≤ C*(1+‖q‖) := by
  obtain ⟨L,hL,large⟩ := large_scale_difference φ
  let M := ∫ z : Space, ‖z‖*‖φ z‖
  let P := ∫ z : Space, ‖φ z‖
  have hM : 0≤M := integral_nonneg fun z => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hP : 0≤P := integral_nonneg fun z => norm_nonneg _
  let A := L + 2*(M+P)
  have hA : 0≤A := by dsimp [A]; positivity
  refine ⟨4*A,by positivity,?_⟩
  intro t ht q h I c hc
  by_cases hz : h = 0
  · subst h
    simp only [sub_zero,sub_self,norm_zero,integral_zero]
    positivity
  have hd : 0<‖h‖ := norm_pos_iff.mpr hz
  let r := fun k : ℕ => (2:ℝ)^k*t
  let S := {z : Space | 2*‖h‖ ≤ ‖z‖}
  let B := fun k => shiftedSpatialKernel φ (r k) q
  let D := A*(1+‖q‖)
  have pos (k : ℕ) : 0<r k := mul_pos (by positivity) ht
  have hD : 0≤D := mul_nonneg hA (by positivity)
  have dL : L ≤ D := by
    dsimp only [D,A]
    nlinarith [norm_nonneg q,mul_nonneg hA (norm_nonneg q)]
  have dM : 2*(M+‖q‖*P) ≤ D := by
    dsimp only [D,A]
    nlinarith [mul_nonneg hL (norm_nonneg q),mul_nonneg hM (norm_nonneg q)]
  have hB (k) : Integrable (B k) := shiftedSpatialKernel_integrable φ (pos k) q
  have diff (k) : Integrable (fun z : Space => B k (z-h) - B k z) := by
    have shift : Integrable (fun z : Space => B k (z-h)) := by
      simpa only [sub_eq_add_neg] using ((measurePreserving_add_right (volume : Measure Space) (-h)).integrable_comp_emb
        (Homeomorph.addRight (-h)).measurableEmbedding).2 (hB k)
    exact shift.sub (hB k)
  have one (k : ℕ) : (∫ z in S, ‖B k (z-h)-B k z‖) ≤ D*min (r k/‖h‖) (‖h‖/r k) := by
    by_cases hk : r k ≤ ‖h‖
    · rw [min_eq_left (((div_le_one hd).mpr hk).trans ((one_le_div (pos k)).mpr hk))]
      have small := exterior_difference_tail φ (r k) (pos k) q h hd
      change _ ≤ 2*(r k/‖h‖)*(M+‖q‖*P) at small
      exact small.trans (by
        rw [mul_right_comm (2:ℝ) (r k / ‖h‖)]
        exact mul_le_mul_of_nonneg_right dM (div_nonneg (pos k).le hd.le))
    · have hh := le_of_not_ge hk
      rw [min_eq_right (((div_le_one (pos k)).mpr hh).trans ((one_le_div hd).mpr hh))]
      exact (setIntegral_le_integral (diff k).norm (Filter.Eventually.of_forall fun z => norm_nonneg _)).trans
        ((large (r k) q h (pos k) hh).trans (mul_le_mul_of_nonneg_right dL (div_nonneg hd.le (pos k).le)))
  let T := fun (k : ℕ) (z : Space) => c k * (B k (z-h)-B k z)
  have hT (k) : Integrable (T k) := (diff k).const_mul _
  have point (z : Space) : ‖∑ k ∈ I, T k z‖ ≤ ∑ k ∈ I, ‖B k (z-h)-B k z‖ := by
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
    dsimp only [T]
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hc k)
  change (∫ z in S, ‖(∑ k ∈ I, c k * B k (z-h)) - (∑ k ∈ I, c k * B k z)‖) ≤ _
  simp_rw [← sum_sub_distrib,← mul_sub]
  change (∫ z in S, ‖∑ k ∈ I, T k z‖) ≤ _
  calc
    _ ≤ ∫ z in S, ∑ k ∈ I, ‖B k (z-h)-B k z‖ :=
      integral_mono (integrable_finset_sum I (fun k _ => hT k)).norm.integrableOn
        (integrable_finset_sum I (fun k _ => (diff k).norm)).integrableOn point
    _ = ∑ k ∈ I, ∫ z in S, ‖B k (z-h)-B k z‖ :=
      integral_finset_sum _ (fun k _ => (diff k).norm.integrableOn)
    _ ≤ ∑ k ∈ I, D*min (r k/‖h‖) (‖h‖/r k) := sum_le_sum fun k _ => one k
    _ ≤ D*4 := by rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (dyadic_difference_sum I t ‖h‖ ht hd) hD
    _ = _ := by dsimp only [D]; ring

end Burnett.Analysis.SignedFourierWindow
