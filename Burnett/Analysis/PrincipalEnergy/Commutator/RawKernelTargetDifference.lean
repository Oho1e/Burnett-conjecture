import Burnett.Analysis.PrincipalEnergy.Quantization.BaseKernelDifference
import Burnett.Analysis.PrincipalEnergy.Quantization.SourceDerivative

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel

/-- Off the diagonal, the actual high-frequency first-order kernel changes
under displacement of the target like one extra inverse power of distance. -/
theorem exists_rawFirstOrderKernel_targetDifference {a : E → E → ℂ}
    (ha : FirstBaseFrequencyOrderOne a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (c x y : E), c ≠ y → ‖x-c‖ ≤ ‖c-y‖ / 2 →
      ‖firstOrderKernel a x (x-y) - firstOrderKernel a c (c-y)‖ ≤
        C * ‖x-c‖ * (‖c-y‖^6)⁻¹ := by
  obtain ⟨D,hD,hder⟩ := exists_firstOrderKernel_relativeDerivative_bound ha.frequency
  obtain ⟨B,hB,hBase⟩ := exists_firstOrderKernel_baseDifference ha
  refine ⟨64*D+B,by positivity,?_⟩
  intro c x y hcy hDistance
  let K := firstOrderKernel a
  let z := c-y
  let w := x-y
  let U := Metric.closedBall z (‖z‖ / 2)
  have hz : z ≠ 0 := sub_ne_zero.mpr hcy
  have hPos := norm_pos_iff.mpr hz
  have hGap : w-z = x-c := by dsimp [w,z]; abel
  have hzU : z ∈ U := Metric.mem_closedBall_self (by positivity)
  have hwU : w ∈ U := by
    simpa only [U,Metric.mem_closedBall,dist_eq_norm,hGap] using hDistance
  have hFar (v : E) (hv : v ∈ U) : ‖z‖ / 2 ≤ ‖v‖ := by
    have hv' : ‖v-z‖ ≤ ‖z‖ / 2 := by
      simpa only [U,Metric.mem_closedBall,dist_eq_norm] using hv
    have ht := norm_sub_le v (v-z)
    rw [sub_sub_cancel] at ht
    linarith
  have hV (v : E) (hv : v ∈ U) : v ≠ 0 := norm_pos_iff.mp ((half_pos hPos).trans_le (hFar v hv))
  have hBound (v : E) (hv : v ∈ U) :
      ‖fderiv ℝ (K x) v‖ ≤ D * ((‖z‖ / 2)^6)⁻¹ :=
    (hder x v (hV v hv)).2.trans (mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (pow_pos (norm_pos_iff.mpr (hV v hv)) _) (pow_pos (half_pos hPos) _)).mpr
      (pow_le_pow_left₀ (by positivity) (hFar v hv) _)) hD)
  have hRel : ‖K x w - K x z‖ ≤ D * ((‖z‖ / 2)^6)⁻¹ * ‖x-c‖ := by
    rw [← hGap]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le (fun v hv => (hder x v (hV v hv)).1)
      hBound (convex_closedBall _ _) hzU hwU
  change ‖K x w - K c z‖ ≤ _
  rw [show K x w - K c z = (K x w - K x z) + (K x z - K c z) by ring]
  refine (norm_add_le _ _).trans ((add_le_add hRel (hBase x c z hz)).trans_eq ?_)
  change D * ((‖z‖ / 2)^6)⁻¹ * ‖x-c‖ + B * ‖x-c‖ * (‖z‖^6)⁻¹ =
    (64*D+B) * ‖x-c‖ * (‖z‖^6)⁻¹
  field_simp [hPos.ne']
  ring

end Burnett.Analysis.FirstOrderDyadic
