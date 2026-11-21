import Burnett.Analysis.PrincipalEnergy.Quantization.SourceDerivative
import Burnett.Analysis.PrincipalEnergy.Quantization.LipschitzKernel
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Burnett.Microlocal.AngularDyadicKernel

theorem coefficientKernel_sourceDifference_le (r : E → ℂ) {L : NNReal}
    (hr : LipschitzWith L r) (k : E → E → ℂ) (C D : ℝ) (hD : 0 ≤ D)
    (hsize : ∀ x z, z ≠ 0 → ‖k x z‖ ≤ C * (‖z‖ ^ 5)⁻¹)
    (hder : ∀ x z, z ≠ 0 → DifferentiableAt ℝ (k x) z ∧ ‖fderiv ℝ (k x) z‖ ≤ D * (‖z‖ ^ 6)⁻¹)
    (x y y' : E) (hxy : x ≠ y) (hGap : ‖y-y'‖ ≤ ‖x-y‖ / 2) :
    ‖coefficientKernel r k x y - coefficientKernel r k x y'‖ ≤
      (L : ℝ) * (C + 96 * D) * ‖y-y'‖ * (‖x-y‖ ^ 5)⁻¹ := by
  let z := x-y
  let z' := x-y'
  let U := Metric.closedBall z (‖z‖ / 2)
  have hz : z ≠ 0 := sub_ne_zero.mpr hxy
  have hp := norm_pos_iff.mpr hz
  have he : z' - z = y-y' := by dsimp [z,z']; abel
  have hzU : z ∈ U := Metric.mem_closedBall_self (by positivity)
  have hz'U : z' ∈ U := by simpa only [U, Metric.mem_closedBall, dist_eq_norm, he] using hGap
  have hU (w : E) (hw : w ∈ U) : ‖z‖ / 2 ≤ ‖w‖ := by
    have hw' : ‖w-z‖ ≤ ‖z‖ / 2 := by
      simpa only [U, Metric.mem_closedBall, dist_eq_norm] using hw
    have ht := norm_sub_le w (w-z)
    rw [sub_sub_cancel] at ht
    linarith
  have hwd (w : E) (hw : w ∈ U) : w ≠ 0 := norm_pos_iff.mp ((half_pos hp).trans_le (hU w hw))
  have hMean (w : E) (hw : w ∈ U) : ‖fderiv ℝ (k x) w‖ ≤ D * ((‖z‖ / 2) ^ 6)⁻¹ :=
    (hder x w (hwd w hw)).2.trans (mul_le_mul_of_nonneg_left
      ((inv_le_inv₀ (pow_pos (norm_pos_iff.mpr (hwd w hw)) _) (pow_pos (half_pos hp) _)).mpr
        (pow_le_pow_left₀ (by positivity) (hU w hw) _)) hD)
  have hK : ‖k x z - k x z'‖ ≤ D * ((‖z‖ / 2)^6)⁻¹ * ‖y-y'‖ := by
    rw [norm_sub_rev (k x z) (k x z'), ← he]
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun w hw => (hder x w (hwd w hw)).1) hMean (convex_closedBall _ _) hzU hz'U
  have hLip (v w : E) : ‖r v - r w‖ ≤ (L : ℝ) * ‖v-w‖ := by
    simpa only [dist_eq_norm] using hr.dist_le_mul v w
  have hz' : ‖z'‖ ≤ 3 * (‖z‖ / 2) := by
    have ht := norm_add_le z (z'-z)
    rw [show z + (z'-z) = z' by abel, he] at ht
    linarith
  have h1 : ‖(r y' - r y) * k x z‖ ≤ ((L : ℝ) * ‖y-y'‖) * (C * (‖z‖^5)⁻¹) := by
    rw [norm_mul, norm_sub_rev (r y') (r y)]
    exact mul_le_mul (hLip y y') (hsize x z hz) (norm_nonneg _) (by positivity)
  have h2 : ‖(r x - r y') * (k x z - k x z')‖ ≤
      ((L : ℝ) * (3 * (‖z‖ / 2))) * (D * ((‖z‖ / 2)^6)⁻¹ * ‖y-y'‖) := by
    rw [norm_mul]
    exact mul_le_mul ((hLip x y').trans (mul_le_mul_of_nonneg_left hz' (by positivity))) hK
      (norm_nonneg _) (by positivity)
  change ‖(r x-r y) * k x z - (r x-r y') * k x z'‖ ≤
    (L : ℝ) * (C + 96 * D) * ‖y-y'‖ * (‖z‖ ^ 5)⁻¹
  have hSplit : (r x-r y) * k x z - (r x-r y') * k x z' =
      (r y'-r y) * k x z + (r x-r y') * (k x z - k x z') := by ring
  rw [hSplit]
  exact (norm_add_le _ _).trans ((add_le_add h1 h2).trans_eq (by
    field_simp [hp.ne']
    ring))

/-- The source-variable Calderón–Zygmund kernel difference is Lipschitz
off the diagonal for the actual high-frequency first-order symbol. -/
theorem exists_firstOrderLipschitzKernel_sourceDifference {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (r : E → ℂ) (L : NNReal), LipschitzWith L r →
      ∀ (x y y' : E), x ≠ y → ‖y-y'‖ ≤ ‖x-y‖ / 2 →
        ‖coefficientKernel r (firstOrderKernel a) x y - coefficientKernel r (firstOrderKernel a) x y'‖ ≤
          (L : ℝ) * K * ‖y-y'‖ * (‖x-y‖ ^ 5)⁻¹ := by
  obtain ⟨p, C, hC, hp, hprofiles⟩ := exists_normalizedInverseProfiles ha
  obtain ⟨D, hD, hder⟩ := exists_firstOrderKernel_relativeDerivative_bound ha
  exact ⟨34*C + 96*D, by positivity, fun r L hr x y y' hxy hGap =>
    coefficientKernel_sourceDifference_le r hr (firstOrderKernel a) _ D hD
      (fun u z hz => ((firstOrderKernel_size a p hp C hC hprofiles u z hz).2 0).2) hder x y y' hxy hGap⟩

end Burnett.Analysis.FirstOrderDyadic
