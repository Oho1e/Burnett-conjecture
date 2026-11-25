import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableCoefficientDerivative
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableCoefficientPacking

set_option autoImplicit false
set_option maxHeartbeats 3850000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory Finset Metric
open scoped ENNReal NNReal BigOperators

private theorem sq_norm_sum_four (v : Fin 4 → ℂ) :
    ‖∑ j, v j‖ₑ^2 ≤ 4*∑ j, ‖v j‖ₑ^2 := by
  have h : ‖∑ j, v j‖^2 ≤ (4 : ℝ)*∑ j, ‖v j‖^2 := by
    have h4 := sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 4 => (1:ℝ)) (fun j => ‖v j‖)
    exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans
      (by simpa only [one_mul,one_pow,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one,Nat.cast_ofNat] using h4)
  have he := ENNReal.ofReal_le_ofReal h
  rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤4),ENNReal.ofReal_pow (norm_nonneg _),
    ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)] at he
  simpa only [ENNReal.ofReal_ofNat,ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm] using he

private theorem derivativeWindow_eq_kernel (a f : SchwartzMap E ℂ) {t : ℝ} (ht : 0<t) (j : ℕ)
    (x : E) : windowTest a f (dyadicScale t j) x = kernelApply (annularKernel a t 0 j) f x := by
  have hs : 0<dyadicScale t j := by unfold dyadicScale; positivity
  have h := windowTest_translate a f (dyadicScale t j) 0 hs x (0 : E)
  simp only [smul_zero,sub_zero,neg_zero,zero_div] at h
  rw [h,shifted_window_physical a f (dyadicScale t j) hs]
  rfl

/-- The scale-normalized real annular part of the original Lipschitz
coefficient satisfies the Carleson packing condition. This estimate uses the
original coefficient's Lipschitz seminorm, with no global L² norm of its derivatives. -/
theorem exists_realAnnularCoefficient_ball_square_packing (profile : SchwartzMap E ℂ)
    (hc : HasCompactSupport (profile : E → ℂ))
    (hprofile : ∀ z, profile z ≠ 0 → 1/2 < ‖z‖ ∧ ‖z‖ < 2) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ (center : E) {R t : ℝ}, 0<R → 0<t → ∀ (J : Finset ℕ),
      (∀ j ∈ J, dyadicScale t j≤R) →
      (∫⁻ x in ball center R, ∑ j ∈ J,
        ENNReal.ofReal (((dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re)^2)) ≤
        C*(L : ℝ≥0∞)^2*volume (ball center R) := by
  obtain ⟨W,hW,res⟩ := exists_coefficientBandpass_derivative_windows profile hc
    (show (0:ℝ)<1/2 by norm_num)
    (fun z hz => ⟨(hprofile z hz).1.le,(hprofile z hz).2.le⟩)
  have compact (k : Fin 4) : HasCompactSupport (W k : E → ℂ) :=
    hc.of_isClosed_subset isClosed_closure (closure_mono fun z hz => hW k z hz)
  choose C finite bound using
    fun k : Fin 4 => exists_annularCoefficient_ball_square_packing (W k) (compact k) (fun z hz => hprofile z (hW k z hz))
  have finSum : (∑ k : Fin 4, C k) < ⊤ := ENNReal.sum_lt_top.mpr fun k _ => finite k
  refine ⟨4*∑ k : Fin 4, C k,ENNReal.mul_lt_top (by norm_num) finSum,?_⟩
  intro D L hD center R t hR ht J hJ
  let U (k : Fin 4) (j : ℕ) (x : E) :=
    kernelApply (annularKernel (W k) t 0 j) (mikhlinDerivative k D) x
  let B := ball center R
  have hU (k : Fin 4) (j : ℕ) : Measurable (U k j) :=
    kernelApply_measurable_ae (annularKernel (W k) t 0 j)
      (by unfold annularKernel shiftedSpatialKernel; fun_prop) (mikhlinDerivative k D)
      (mikhlinDerivative k D).continuous.aestronglyMeasurable
  have point (j : ℕ) (x : E) :
      ENNReal.ofReal (((dyadicScale t j)⁻¹*(windowTest profile D (dyadicScale t j) x).re)^2) ≤
        4*∑ k : Fin 4, ‖U k j x‖ₑ^2 := by
    let s := dyadicScale t j
    have hpos : 0<s := by unfold s dyadicScale; positivity
    have he := congrArg (fun M : SchwartzMap E ℂ => M x) (res D hpos)
    change (((s⁻¹ : ℝ) : ℂ) • windowTest profile D s) x =
      (∑ k : Fin 4, windowTest (W k) (mikhlinDerivative k D) s) x at he
    rw [SchwartzMap.smul_apply,smul_eq_mul,coefficientSchwartz_sum_value] at he
    have hv : ((s⁻¹ : ℝ) : ℂ)*windowTest profile D s x = ∑ k : Fin 4, U k j x := by
      simpa only [U,s,derivativeWindow_eq_kernel _ _ ht] using he
    have hre : (((s⁻¹ : ℝ) : ℂ)*windowTest profile D s x).re = s⁻¹*(windowTest profile D s x).re := by
      simp [Complex.mul_re]
    have habs : |s⁻¹*(windowTest profile D s x).re| ≤ ‖∑ k : Fin 4, U k j x‖ := by
      rw [← hre,hv]
      exact Complex.abs_re_le_norm _
    have h2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at h2
    refine (ENNReal.ofReal_le_ofReal h2).trans ?_
    rw [ENNReal.ofReal_pow (norm_nonneg _),ofReal_norm_eq_enorm]
    exact sq_norm_sum_four _
  have each (k : Fin 4) : (∫⁻ x in B, ∑ j ∈ J, ‖U k j x‖ₑ^2) ≤ C k*(L : ℝ≥0∞)^2*volume B :=
    bound k (mikhlinDerivative k D) (mikhlinDerivative k D).continuous.measurable L
      (mikhlinDerivative_norm_le_lipschitz D hD k) center hR ht J hJ
  calc
    _ ≤ ∫⁻ x in B, 4*∑ k : Fin 4, ∑ j ∈ J, ‖U k j x‖ₑ^2 := by
      refine lintegral_mono fun x => ?_
      rw [show (∑ k : Fin 4, ∑ j ∈ J, ‖U k j x‖ₑ^2) =
        (∑ j ∈ J, ∑ k : Fin 4, ‖U k j x‖ₑ^2) from sum_comm,mul_sum]
      exact sum_le_sum fun j _ => point j x
    _ = 4*∑ k : Fin 4, ∫⁻ x in B, ∑ j ∈ J, ‖U k j x‖ₑ^2 := by
      rw [lintegral_const_mul' _ _ (by norm_num),
        lintegral_finset_sum _ (fun k _ => measurable_sum _ (fun j _ => (hU k j).enorm.pow_const _))]
    _ ≤ 4*∑ k : Fin 4, C k*(L : ℝ≥0∞)^2*volume B :=
      mul_le_mul_left' (sum_le_sum fun k _ => each k) 4
    _ = _ := by rw [← sum_mul,← sum_mul]; ac_rfl

end Burnett.A06
