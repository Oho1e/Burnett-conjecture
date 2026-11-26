import Burnett.Geometry.Causality.ChartTimeOrientation

set_option autoImplicit false

noncomputable section

namespace Burnett.Geometry.FiniteCausalVolume

open Set
open scoped ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The timelike component dominates the error from evaluating a causal
velocity at a shifted point. The negative quadratic term also covers zero
velocity. -/
theorem timelike_of_dominating_time_push (B : LinearMap.BilinForm ℝ E) (hS : B.IsSymm)
    (n v : E) {c e α : ℝ} (hc : 0 < c) (hα : 0 < α) (hn : B n n < 0)
    (hcone : B n v ≤ -c * ‖v‖) (hshift : B v v ≤ e * ‖v‖ ^ 2)
    (hdom : e * ‖v‖ ≤ c * α) :
    B (v + α • n) (v + α • n) < 0 ∧ B n (v + α • n) < 0 := by
  have hpart : B v v ≤ c * α * ‖v‖ := hshift.trans (by
    rw [pow_two, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hdom (norm_nonneg v))
  have hmix := mul_le_mul_of_nonneg_left hcone (show 0 ≤ 2 * α by positivity)
  have hbase : B v v + 2 * α * B n v ≤ 0 := by
    have hpos : 0 ≤ c * α * ‖v‖ := by positivity
    linarith [show 2 * α * (-c * ‖v‖) = -(2 * (c * α * ‖v‖)) by ring]
  have hnterm : α ^ 2 * B n n < 0 := mul_neg_of_pos_of_neg (sq_pos_of_pos hα) hn
  constructor
  · calc
      B (v + α • n) (v + α • n) = B v v + 2 * α * B n v + α ^ 2 * B n n := by
        simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hS.eq v n]
        ring
      _ < 0 := add_neg_of_nonpos_of_neg hbase hnterm
  · simp only [map_add, map_smul, smul_eq_mul]
    exact add_neg_of_nonpos_of_neg (hcone.trans (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le)
      (norm_nonneg v))) (mul_neg_of_pos_of_neg hα hn)

/-- A shift that vanishes at the final time and always adds a dominating
future component to the velocity. -/
def endpointTimePush (k b t : ℝ) : ℝ := 1 - Real.exp (k * (b - t))

theorem endpointTimePush_hasDeriv (k b t : ℝ) :
    HasDerivAt (endpointTimePush k b) (k * Real.exp (k * (b - t))) t := by
  have h : HasDerivAt (fun s : ℝ => k * (b - s)) (-k) t := by
    convert ((hasDerivAt_id t).const_sub b).const_mul k using 1
    ring
  convert h.exp.const_sub 1 using 1
  ring

theorem endpointTimePush_dominates {k b t : ℝ} (hk : 0 < k) (ht : t ≤ b) :
    endpointTimePush k b b = 0 ∧ endpointTimePush k b t ≤ 0 ∧
      0 < k * Real.exp (k * (b - t)) ∧
      k * |endpointTimePush k b t| ≤ k * Real.exp (k * (b - t)) := by
  have hexp : 1 ≤ Real.exp (k * (b - t)) := Real.one_le_exp_iff.mpr
    (mul_nonneg hk.le (sub_nonneg.mpr ht))
  have hnonpos : endpointTimePush k b t ≤ 0 := sub_nonpos.mpr hexp
  refine ⟨by simp [endpointTimePush], hnonpos, mul_pos hk (Real.exp_pos _), ?_⟩
  rw [abs_of_nonpos hnonpos]
  apply mul_le_mul_of_nonneg_left _ hk.le
  change -(1 - Real.exp (k * (b - t))) ≤ Real.exp (k * (b - t))
  linarith

end Burnett.Geometry.FiniteCausalVolume
