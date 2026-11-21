import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyKernel
import Burnett.Analysis.PrincipalEnergy.Quantization.BaseDerivative

set_option autoImplicit false
set_option maxHeartbeats 2100000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Bornology Set Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators ContDiff FourierTransform

private theorem low_cutoff_support :
    tsupport (fun ξ : E => (radialCore ξ : ℂ)) ⊆ Metric.closedBall 0 2 := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro ξ hξ
  by_contra h
  have hz : 2 ≤ ‖ξ‖ :=
    (not_le.mp (by simpa only [Metric.mem_closedBall,dist_zero_right] using h)).le
  exact hξ (by simp [radialCore_eq_zero ξ hz])

/-- Multiplication by the original fixed radial cutoff gives a bounded
family of inverse-Fourier Schwartz profiles from derivative bounds on its support. -/
theorem exists_fixedLowInverseProfiles {ι : Type*} (F : ι → E → ℂ)
    (hSmooth : ∀ u, ContDiff ℝ ∞ (F u))
    (hOrder : ∀ n : ℕ, ∃ C : ℝ, 0≤C ∧ ∀ u ξ, ‖ξ‖≤2 →
      ‖iteratedFDeriv ℝ n (F u) ξ‖≤C) :
    ∃ p : ι → SchwartzMap E ℂ,
      (∀ u, (p u : E → ℂ) = 𝓕⁻ (fun ξ => (radialCore ξ : ℂ)*F u ξ)) ∧
      IsVonNBounded ℝ (Set.range p) := by
  classical
  let c : E → ℂ := fun ξ => (radialCore ξ : ℂ)
  have hc : ContDiff ℝ ∞ c := Complex.ofRealCLM.contDiff.comp radialCore_contDiff
  have hK : IsCompact (Metric.closedBall (0:E) 2) := isCompact_closedBall _ _
  have hcSupp : HasCompactSupport c := hK.of_isClosed_subset isClosed_closure low_cutoff_support
  let χ := hcSupp.toSchwartzMap hc
  let G (u : ι) (ξ : E) := c ξ*F u ξ
  have hG (u : ι) : tsupport (G u) ⊆ Metric.closedBall (0:E) 2 := by
    have hSupport : Function.support (G u) ⊆ Function.support c := by
      intro ξ hξ hz
      apply hξ
      change c ξ*F u ξ=0
      rw [show c ξ=0 from hz,zero_mul]
    exact (closure_mono hSupport).trans low_cutoff_support
  have hGS (u : ι) : HasCompactSupport (G u) := hK.of_isClosed_subset isClosed_closure (hG u)
  let q (u : ι) := (hGS u).toSchwartzMap (hc.mul (hSmooth u))
  have hq : IsVonNBounded ℝ (Set.range q) := by
    rw [← image_univ]
    apply ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded q).mpr
    rintro ⟨k,n⟩
    choose M hM hFirst using hOrder
    let C := ∑ i ∈ Finset.range (n+1), (n.choose i : ℝ)*SchwartzMap.seminorm ℝ 0 i χ*M (n-i)
    have hC : 0≤C := Finset.sum_nonneg fun i _ => mul_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _)) (hM (n-i))
    have hConst : 0≤(2:ℝ)^k*C := mul_nonneg (by positivity) hC
    refine ⟨(2:ℝ)^k*C+1,add_pos_of_nonneg_of_pos hConst zero_lt_one,fun u _ => ?_⟩
    apply lt_of_le_of_lt (SchwartzMap.seminorm_le_bound ℝ k n (q u) hConst ?_) (lt_add_one _)
    intro ξ
    by_cases hx : ξ ∈ tsupport (G u)
    · have hξ : ‖ξ‖≤2 := by simpa only [Metric.mem_closedBall,dist_zero_right] using hG u hx
      have hn : (n : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
      change ‖ξ‖^k*‖iteratedFDeriv ℝ n (G u) ξ‖≤_
      refine mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hξ _) ?_ (norm_nonneg _) (by positivity)
      refine (norm_iteratedFDeriv_mul_le hc (hSmooth u) ξ hn).trans (Finset.sum_le_sum fun i _ => ?_)
      have hi : ‖iteratedFDeriv ℝ i c ξ‖≤SchwartzMap.seminorm ℝ 0 i χ :=
        SchwartzMap.norm_iteratedFDeriv_le_seminorm ℝ χ i ξ
      exact mul_le_mul (mul_le_mul_of_nonneg_left hi (Nat.cast_nonneg _)) (hFirst _ u ξ hξ)
        (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (apply_nonneg _ _))
    · have hZero : iteratedFDeriv ℝ n (G u) ξ=0 := by
        by_contra hn
        exact hx (support_iteratedFDeriv_subset n hn)
      change ‖ξ‖^k*‖iteratedFDeriv ℝ n (G u) ξ‖≤_
      simpa only [hZero,norm_zero,mul_zero] using hConst
  let V := (SchwartzMap.fourierTransformCLE ℝ (V := E) (E := ℂ)).symm
  refine ⟨V ∘ q,?_,?_⟩
  · intro u
    funext ξ
    simp only [Function.comp_apply,V,SchwartzMap.fourierTransformCLE_symm_apply]
    rfl
  · rw [Set.range_comp]
    exact hq.image V.toContinuousLinearMap

theorem exists_firstOrderLowKernel_profiles {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ p : E → SchwartzMap E ℂ,
      (∀ x, (p x : E → ℂ) = firstOrderLowKernel a x) ∧
      IsVonNBounded ℝ (Set.range p) := by
  refine exists_fixedLowInverseProfiles a ha.smooth fun n => ?_
  obtain ⟨C,hC,hB⟩ := ha.order n
  refine ⟨3*C,mul_nonneg (by norm_num) hC,fun x ξ hξ => ?_⟩
  have hW : 1 ≤ (1+‖ξ‖)^n := one_le_pow₀ (le_add_of_nonneg_right (norm_nonneg _))
  calc
    _ ≤ ‖iteratedFDeriv ℝ n (a x) ξ‖*(1+‖ξ‖)^n := le_mul_of_one_le_right (norm_nonneg _) hW
    _ ≤ C*(1+‖ξ‖) := hB x ξ
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left (by linarith : 1+‖ξ‖≤3) hC
      linarith

/-- The genuine low kernel and its relative derivative have the inverse
powers required by the original four-dimensional commutator test. -/
theorem exists_firstOrderLowKernel_relative_bounds {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ C D : ℝ, 0≤C ∧ 0≤D ∧
      (∀ x z, z≠0 → ‖firstOrderLowKernel a x z‖≤C*(‖z‖^5)⁻¹) ∧
      (∀ x z, z≠0 → DifferentiableAt ℝ (firstOrderLowKernel a x) z ∧
        ‖fderiv ℝ (firstOrderLowKernel a x) z‖≤D*(‖z‖^6)⁻¹) := by
  obtain ⟨p,hp,hP⟩ := exists_firstOrderLowKernel_profiles ha
  let q := SchwartzMap.fderivCLM ℝ ∘ p
  have hQ : IsVonNBounded ℝ (Set.range q) := by rw [Set.range_comp]; exact hP.image (SchwartzMap.fderivCLM ℝ)
  rw [← image_univ] at hP hQ
  have hPb := ((schwartz_withSeminorms ℝ E ℂ).image_isVonNBounded_iff_seminorm_bounded p).mp hP
  have hQb := ((schwartz_withSeminorms ℝ E (E →L[ℝ] ℂ)).image_isVonNBounded_iff_seminorm_bounded q).mp hQ
  obtain ⟨C,hC,hSize⟩ := hPb (5,0)
  obtain ⟨D,hD,hDer⟩ := hQb (6,0)
  refine ⟨C,D,hC.le,hD.le,?_,?_⟩
  · intro x z hz
    rw [← hp x,← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hz) _)).mpr
    rw [mul_comm]
    exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ (p x) 5 z).trans (hSize x trivial).le
  · intro x z hz
    rw [← hp x]
    refine ⟨(p x).differentiableAt,?_⟩
    change ‖q x z‖≤D*(‖z‖^6)⁻¹
    rw [← div_eq_mul_inv]
    apply (le_div_iff₀ (pow_pos (norm_pos_iff.mpr hz) _)).mpr
    rw [mul_comm]
    exact (SchwartzMap.norm_pow_mul_le_seminorm ℝ (q x) 6 z).trans (hDer x trivial).le

end Burnett.Analysis.FirstOrderDyadic
