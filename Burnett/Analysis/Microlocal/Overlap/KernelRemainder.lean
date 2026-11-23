import Burnett.Analysis.Microlocal.Overlap.KernelGeometry
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open Set

section TaylorEstimate

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The derivative is frozen at the first kernel variable. -/
theorem transition_taylor_remainder {K : Set E} (hConv : Convex ℝ K) (Φ : E → F)
    (hΦ : ∀ x ∈ K, DifferentiableAt ℝ Φ x) {L : ℝ} (hL : 0 ≤ L)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ Φ y - fderiv ℝ Φ x‖ ≤ L * ‖y - x‖)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) :
    ‖(Φ x - Φ y) - fderiv ℝ Φ x (x - y)‖ ≤ L * ‖x - y‖ ^ 2 := by
  let A := fderiv ℝ Φ x
  let f (z : E) := Φ z - A z
  let S := K ∩ Metric.closedBall x ‖x - y‖
  have hS : Convex ℝ S := hConv.inter (convex_closedBall _ _)
  have hxS : x ∈ S := ⟨hx, Metric.mem_closedBall_self (norm_nonneg _)⟩
  have hyS : y ∈ S := ⟨hy, by rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]⟩
  have hDeriv (z : E) (hz : z ∈ S) : HasFDerivAt f (fderiv ℝ Φ z - A) z :=
    (hΦ z hz.1).hasFDerivAt.sub A.hasFDerivAt
  have hBound (z : E) (hz : z ∈ S) : ‖fderiv ℝ f z‖ ≤ L * ‖x - y‖ := by
    rw [(hDeriv z hz).fderiv]
    have hz' := hz.2
    rw [Metric.mem_closedBall, dist_eq_norm] at hz'
    exact (hLip x hx z hz.1).trans (mul_le_mul_of_nonneg_left hz' hL)
  have h := hS.norm_image_sub_le_of_norm_fderiv_le
    (fun z hz => (hDeriv z hz).differentiableAt) hBound hyS hxS
  have heq : f x - f y = (Φ x - Φ y) - A (x - y) := by
    dsimp only [f]
    rw [map_sub]
    abel
  rwa [heq, mul_assoc, ← pow_two] at h

/-- Throughout the interpolation segment, the Taylor error is smaller than
half of the lower bound for the frozen linear argument. -/
theorem segment_of_kernel_arguments_lower {q r : ℝ} {u v : F}
    (hv : q * r ≤ ‖v‖) (hsmall : ‖u - v‖ ≤ q / 2 * r)
    {z : F} (hz : z ∈ segment ℝ v u) :
    q / 2 * r ≤ ‖z‖ := by
  have hdist := (norm_sub_le_of_mem_segment hz).trans hsmall
  have htri : ‖v‖ ≤ ‖z‖ + ‖z - v‖ := by
    rw [norm_sub_rev z v]
    have he : z + (v - z) = v := by abel
    simpa only [he] using norm_add_le z (v - z)
  linarith

end TaylorEstimate

section Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The localized half-density kernel minus the kernel of the frozen
Jacobian at its output variable. -/
def halfDensityKernelDifference (Φ : E → E) (w : E → ℝ) (k : E → ℂ)
    (x y : E) : ℂ :=
  (w x * w y) • k (Φ x - Φ y) - (w x)^2 • k (fderiv ℝ Φ x (x - y))

omit [NormedSpace ℝ E] in
private theorem decay_le_div {s a C : ℝ} {z : E} {n : ℕ} {v : ℝ}
    (hs : 0 ≤ s) (ha : 0 ≤ a) (hz : a ≤ ‖z‖)
    (hv : 0 ≤ v) (h : (1 + s * ‖z‖)^n * v ≤ C) :
    v ≤ C / (1 + s * a)^n := by
  apply (le_div_iff₀ (pow_pos (by positivity) _)).2
  rw [mul_comm v]
  apply le_trans _ h
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (by positivity) (by gcongr) _) hv

/-- Rapid decay of one shell and its first derivative gives one power of
scale gain for the near kernel. The remaining fifth power is integrable
in dimension four. -/
theorem halfDensityKernelDifference_near_bound
    {K : Set E} (hConv : Convex ℝ K) (Φ : E → E) (w : E → ℝ) (k : E → ℂ)
    (hΦ : ∀ x ∈ K, DifferentiableAt ℝ Φ x) (hk : Differentiable ℝ k)
    {q L W H s C₀ C₁ : ℝ} (hq : 0 < q) (hL : 0 ≤ L) (hW : 0 ≤ W)
    (hH : 0 ≤ H) (hs : 0 < s) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
    (hLip : ∀ x ∈ K, ∀ y ∈ K, ‖fderiv ℝ Φ y - fderiv ℝ Φ x‖ ≤ L * ‖y - x‖)
    (hInv : ∀ x ∈ K, ∀ v, q * ‖v‖ ≤ ‖fderiv ℝ Φ x v‖)
    (hWeight : ∀ x ∈ K, ‖w x‖ ≤ W)
    (hWeightLip : ∀ x ∈ K, ∀ y ∈ K, ‖w y - w x‖ ≤ H * ‖x - y‖)
    (hSize : ∀ z, (1 + s * ‖z‖)^7 * ‖k z‖ ≤ C₀ * s^4)
    (hDerivative : ∀ z, (1 + s * ‖z‖)^7 * ‖fderiv ℝ k z‖ ≤ C₁ * s^5)
    {x y : E} (hx : x ∈ K) (hy : y ∈ K) (hNear : L * ‖x - y‖ ≤ q / 2) :
    ‖halfDensityKernelDifference Φ w k x y‖ ≤
      (W * H * C₀ / (q / 2) + W^2 * C₁ * L / (q / 2)^2) * s^3 /
        (1 + s * (q / 2) * ‖x - y‖)^5 := by
  let r := ‖x - y‖
  let a := q / 2
  let D := 1 + s * a * r
  let u := Φ x - Φ y
  let v := fderiv ℝ Φ x (x - y)
  have hr : 0 ≤ r := norm_nonneg _
  have ha : 0 < a := half_pos hq
  have hD : 0 < D := by dsimp only [D]; positivity
  have hD1 : 1 ≤ D := le_add_of_nonneg_right (mul_nonneg (mul_nonneg hs.le ha.le) hr)
  have hTaylor : ‖u - v‖ ≤ L * r^2 :=
    transition_taylor_remainder hConv Φ hΦ hL hLip hx hy
  have hSmall : ‖u - v‖ ≤ a * r := hTaylor.trans (calc
    L * r^2 = (L * r) * r := by ring
    _ ≤ a * r := mul_le_mul_of_nonneg_right hNear hr)
  have hSegment (z : E) (hz : z ∈ segment ℝ v u) : a * r ≤ ‖z‖ :=
    segment_of_kernel_arguments_lower (hInv x hx (x - y)) hSmall hz
  have hku : ‖k u‖ ≤ C₀ * s^4 / D^7 := by
    have h := decay_le_div hs.le (mul_nonneg ha.le hr) (hSegment u (right_mem_segment ℝ _ _))
      (norm_nonneg (k u)) (hSize u)
    simpa only [D, mul_assoc] using h
  have hk' (z : E) (hz : z ∈ segment ℝ v u) : ‖fderiv ℝ k z‖ ≤ C₁ * s^5 / D^7 := by
    have h := decay_le_div hs.le (mul_nonneg ha.le hr) (hSegment z hz)
      (norm_nonneg (fderiv ℝ k z)) (hDerivative z)
    simpa only [D, mul_assoc] using h
  have hDiff : ‖k u - k v‖ ≤ (C₁ * s^5 / D^7) * (L * r^2) := by
    have hConv' : Convex ℝ (segment ℝ v u) := convex_segment v u
    exact (hConv'.norm_image_sub_le_of_norm_fderiv_le
      (fun z _ => hk z) hk' (left_mem_segment ℝ _ _) (right_mem_segment ℝ _ _)).trans
      (mul_le_mul_of_nonneg_left hTaylor (by positivity))
  have hsplit : halfDensityKernelDifference Φ w k x y =
      (w x * (w y - w x)) • k u + (w x)^2 • (k u - k v) := by
    unfold halfDensityKernelDifference
    change (w x * w y) • k u - (w x)^2 • k v = _
    simp only [mul_sub, pow_two, sub_smul, smul_sub]
    abel
  have hLinear : r ≤ D / (s * a) := by
    apply (le_div_iff₀ (mul_pos hs ha)).2
    rw [mul_comm r]
    exact le_add_of_nonneg_left zero_le_one
  have hSquared : r^2 ≤ (D / (s * a))^2 := pow_le_pow_left₀ hr hLinear 2
  have hLarger : r ≤ D^2 / (s * a) := by
    apply hLinear.trans
    apply div_le_div_of_nonneg_right _ (mul_nonneg hs.le ha.le)
    simpa only [one_mul, pow_two] using mul_le_mul_of_nonneg_right hD1 hD.le
  have hTerms := norm_add_le ((w x * (w y - w x)) • k u)
    ((w x)^2 • (k u - k v))
  rw [hsplit]
  apply hTerms.trans
  simp only [norm_smul, norm_mul, norm_pow]
  calc
    _ ≤ (W * (H * r)) * (C₀ * s^4 / D^7) +
          W^2 * ((C₁ * s^5 / D^7) * (L * r^2)) := by
      exact add_le_add
        (mul_le_mul
          (mul_le_mul (hWeight x hx) (hWeightLip x hx y hy) (norm_nonneg _) hW)
          hku (norm_nonneg _) (mul_nonneg hW (mul_nonneg hH hr)))
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hWeight x hx) 2)
          hDiff (norm_nonneg _) (sq_nonneg _))
    _ ≤ (W * (H * (D^2 / (s * a)))) * (C₀ * s^4 / D^7) +
          W^2 * ((C₁ * s^5 / D^7) * (L * (D / (s * a))^2)) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hLarger hH) hW) (by positivity))
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSquared hL) (by positivity))
          (sq_nonneg _))
    _ = (W * H * C₀ / a + W^2 * C₁ * L / a^2) * s^3 / D^5 := by
      field_simp [hs.ne', ha.ne', hD.ne']

/-- On the far part both kernel arguments have a positive uniform
separation from zero, so no first derivative estimate is needed. -/
theorem halfDensityKernelDifference_far_bound
    (Φ : E → E) (w : E → ℝ) (k : E → ℂ) {W s C₀ a : ℝ}
    (hW : 0 ≤ W) (hs : 0 < s) (ha : 0 ≤ a)
    (hSize : ∀ z, (1 + s * ‖z‖)^7 * ‖k z‖ ≤ C₀ * s^4)
    {x y : E} (hx : ‖w x‖ ≤ W) (hy : ‖w y‖ ≤ W)
    (hu : a ≤ ‖Φ x - Φ y‖) (hv : a ≤ ‖fderiv ℝ Φ x (x - y)‖) :
    ‖halfDensityKernelDifference Φ w k x y‖ ≤ 2 * W^2 * (C₀ * s^4 / (1 + s * a)^7) := by
  let u := Φ x - Φ y
  let v := fderiv ℝ Φ x (x - y)
  let C := C₀ * s^4 / (1 + s * a)^7
  have hku : ‖k u‖ ≤ C := decay_le_div hs.le ha hu (norm_nonneg _) (hSize u)
  have hkv : ‖k v‖ ≤ C := decay_le_div hs.le ha hv (norm_nonneg _) (hSize v)
  unfold halfDensityKernelDifference
  change ‖(w x * w y) • k u - (w x)^2 • k v‖ ≤ 2 * W^2 * C
  apply (norm_sub_le _ _).trans
  simp only [norm_smul, norm_mul, norm_pow]
  calc
    _ ≤ (W * W) * C + W^2 * C := by
      exact add_le_add
        (mul_le_mul (mul_le_mul hx hy (norm_nonneg _) hW) hku (norm_nonneg _) (by positivity))
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hx 2) hkv (norm_nonneg _) (sq_nonneg _))
    _ = _ := by ring

end Pointwise

end Burnett.Microlocal.OverlapKernel
