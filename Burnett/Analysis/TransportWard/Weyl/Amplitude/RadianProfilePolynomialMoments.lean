import Burnett.Analysis.TransportWard.Weyl.Amplitude.WeightedParameterJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.ClassicalAmplitudeShift

set_option autoImplicit false
set_option maxHeartbeats 3700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology

theorem integrable_radian_shift_polynomial_decay (k : ℕ) :
    Integrable (fun η : E =>
      (1+‖η‖) ^ (-(((volume : Measure E).integrablePower + k : ℕ) : ℝ))*(1+tau*‖η‖)^k) volume := by
  let r := (volume : Measure E).integrablePower
  let w (η : E) : ℝ := (1+‖η‖) ^ (-((r+k : ℕ) : ℝ))*(1+tau*‖η‖)^k
  have τ : 0 ≤ tau := mul_nonneg (by norm_num) Real.pi_pos.le
  have cw : Continuous w := ((continuous_const.add continuous_norm).rpow_const
    (fun η => Or.inl (by positivity))).mul ((continuous_const.add (continuous_const.mul continuous_norm)).pow k)
  change Integrable w volume
  apply ((SchwartzMap.integrable_pow_neg_integrablePower (volume : Measure E)).const_mul ((1+tau)^k)).mono'
    cw.aestronglyMeasurable
  filter_upwards with η
  have w0 : 0 ≤ w η := mul_nonneg (Real.rpow_nonneg (by positivity) _) (by positivity)
  rw [Real.norm_of_nonneg w0]
  have per : 1+tau*‖η‖ ≤ (1+tau)*(1+‖η‖) := by nlinarith only [τ,norm_nonneg η]
  have normA : 0 ≤ 1+tau*‖η‖ := by positivity
  have pw := pow_le_pow_left₀ normA per k
  rw [mul_pow] at pw
  have expE : (1+‖η‖) ^ (-((r+k : ℕ) : ℝ))*(1+‖η‖)^k = (1+‖η‖) ^ (-(r : ℝ)) := by
    rw [← Real.rpow_natCast,← Real.rpow_add (by positivity)]
    congr 1
    push_cast
    ring
  calc
    _ ≤ (1+‖η‖) ^ (-((r+k : ℕ) : ℝ))*((1+tau)^k*(1+‖η‖)^k) :=
      mul_le_mul_of_nonneg_left pw (Real.rpow_nonneg (by positivity) _)
    _ = (1+tau)^k*((1+‖η‖) ^ (-((r+k : ℕ) : ℝ))*(1+‖η‖)^k) := by ring
    _ = _ := by rw [expE]

end Burnett.A03
