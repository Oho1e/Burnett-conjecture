import Burnett.Analysis.PrincipalEnergy.Commutator.HighConstantSubtraction
import Burnett.Analysis.PrincipalEnergy.Commutator.RawKernelTargetDifference
import Burnett.Analysis.PrincipalEnergy.Commutator.InverseFifthTail

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Metric Filter Burnett.Microlocal.AngularDyadicKernel

/-- The high-frequency first-order action on an input constant on the
doubled ball has uniform oscillation on the inner ball. The input's deviation
from its local constant can grow at the Lip scale, with no second derivatives. -/
theorem exists_firstOrderHighAction_far_oscillation {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (g χ : SchwartzMap E ℂ)
      (_hχC : HasCompactSupport (χ : E → ℂ))
      (_hχOne : ∀ y : E, ‖y‖ ≤ 1 → χ y = 1) (_hχBound : ∀ y : E, ‖χ y‖ ≤ 1)
      (c x : E) (q : ℂ) (R L : ℝ), 0 < R → 0 ≤ L →
      (∀ y ∈ ball c (2*R), g y = q) →
      (∀ y, ‖g y-q‖ ≤ L * ‖c-y‖) → ‖x-c‖ ≤ R →
      ‖firstOrderHighAction a g x - firstOrderHighAction a g c‖ ≤ D * L := by
  obtain ⟨C,hC,hKernel⟩ := exists_rawFirstOrderKernel_targetDifference ha
  let J := ∫ z : E, inverseFifthTail 1 z
  have hJ : 0 ≤ J := integral_nonneg (inverseFifthTail_nonneg 1)
  refine ⟨C*J/2,by positivity,?_⟩
  intro g χ hχC hχOne hχBound c x q R L hR hL hNear hGrowth hx
  have hNearX (y : E) (hy : y ∈ ball x R) : g y = q := by
    apply hNear y
    have hyx : ‖y-x‖ < R := by simpa only [mem_ball,dist_eq_norm] using hy
    have ht := norm_add_le (y-x) (x-c)
    rw [show y-x+(x-c)=y-c by abel] at ht
    rw [mem_ball,dist_eq_norm]
    linarith
  have hTwo : 0 < 2*R := by positivity
  obtain ⟨hIntX,hEqX⟩ := firstOrderHighAction_eq_kernel_sub_constant ha.frequency g χ
    hχC hχOne hχBound x q R hR hNearX
  obtain ⟨hIntC,hEqC⟩ := firstOrderHighAction_eq_kernel_sub_constant ha.frequency g χ
    hχC hχOne hχBound c q (2*R) hTwo hNear
  let k (y : E) := (firstOrderKernel a x (x-y) - firstOrderKernel a c (c-y)) * (g y-q)
  have hIDiff : (fun y => firstOrderKernel a x (x-y) * (g y-q) -
      firstOrderKernel a c (c-y) * (g y-q)) = k := by
    funext y
    change _ = (firstOrderKernel a x (x-y) - firstOrderKernel a c (c-y)) * (g y-q)
    ring
  have hPoint (y : E) : ‖k y‖ ≤ (C*L*‖x-c‖) * inverseFifthTail (2*R) (c-y) := by
    by_cases hy : y ∈ ball c (2*R)
    · change ‖(firstOrderKernel a x (x-y) - firstOrderKernel a c (c-y)) * (g y-q)‖ ≤ _
      rw [hNear y hy,sub_self,mul_zero,norm_zero]
      exact mul_nonneg (by positivity) (inverseFifthTail_nonneg _ _)
    have hSep : 2*R ≤ ‖c-y‖ := by
      simpa only [mem_ball,dist_comm y c,dist_eq_norm,not_lt] using hy
    have hcy := norm_pos_iff.mp (hTwo.trans_le hSep)
    have hGap : ‖x-c‖ ≤ ‖c-y‖/2 := by linarith
    have hPos : 0 < ‖c-y‖ := norm_pos_iff.mpr hcy
    have hk := hKernel c x y (sub_ne_zero.mp hcy) hGap
    change ‖(firstOrderKernel a x (x-y) - firstOrderKernel a c (c-y)) * (g y-q)‖ ≤ _
    rw [norm_mul, inverseFifthTail,if_pos hSep]
    exact (mul_le_mul hk (hGrowth y) (norm_nonneg _) (by positivity)).trans_eq (by
      field_simp [hPos.ne'])
  have hkI : Integrable k := by
    rw [← hIDiff]
    exact hIntX.sub hIntC
  obtain ⟨hTail,hScale⟩ := inverseFifthTail_about_center hTwo c
  have hBoundInt : Integrable (fun y => (C*L*‖x-c‖) * inverseFifthTail (2*R) (c-y)) :=
    hTail.const_mul _
  rw [hEqX,hEqC,← integral_sub hIntX hIntC]
  change ‖∫ y, (fun y => firstOrderKernel a x (x-y) * (g y-q) -
    firstOrderKernel a c (c-y) * (g y-q)) y‖ ≤ _
  rw [hIDiff]
  calc
    _ ≤ ∫ y, ‖k y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, (C*L*‖x-c‖) * inverseFifthTail (2*R) (c-y) :=
      integral_mono hkI.norm hBoundInt hPoint
    _ = (C*L*‖x-c‖) * ((2*R)⁻¹ * J) := by simp only [integral_const_mul,hScale,J]
    _ = (C*L*J) * (‖x-c‖ * (2*R)⁻¹) := by ring
    _ ≤ (C*L*J) * (1/2) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      rw [← div_eq_mul_inv]
      apply (div_le_iff₀ hTwo).mpr
      linarith
    _ = _ := by ring

end Burnett.Analysis.FirstOrderDyadic
