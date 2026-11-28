import Burnett.Analysis.TransportWard.Weyl.CoefficientTaylorIntegrandJoint

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 1700

noncomputable section

namespace Burnett.V03

open Function MeasureTheory Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.CarlesonEmbedding (integrable_schwartz_weighted)
open scoped ContDiff FourierTransform

local notation "P" => RadianParameter
local notation "W" => radianFrequencyWeight

theorem coefficientTaylorIntegrand_section_smooth {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (c : SchwartzMap E ℂ) (e : E) :
    ContDiff ℝ ∞ (coefficientTaylorIntegrand a c e) := by
  let U (p : P) := patchFourierPhase e p.1
  let V (p : P) := linearTaylorRemainder (a p.1) p.2 e
  have hU : ContDiff ℝ ∞ U := (radian_base_phase_smooth e).comp contDiff_fst
  have hV : ContDiff ℝ ∞ V :=
    (linearTaylorRemainder_symbol_parameter_smooth ha).comp (contDiff_const.prodMk contDiff_id)
  change ContDiff ℝ ∞ (fun p : P => (U p * 𝓕 (c : E → ℂ) e) * V p)
  exact (hU.mul contDiff_const).mul hV

theorem coefficientTaylorIntegrand_section_measurable {a : E → E → ℂ}
    (ha : ContDiff ℝ ∞ (uncurry a)) (c : SchwartzMap E ℂ) (n : ℕ) (p : P) :
    AEStronglyMeasurable (fun e => iteratedFDeriv ℝ n (coefficientTaylorIntegrand a c e) p)
      (volume : Measure E) :=
  ((smooth_right_slice_iterated_fderiv (coefficientTaylorIntegrand a c)
    (coefficientTaylorIntegrand_joint_smooth ha c) n).continuous.comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable

theorem coefficientTaylorIntegrand_integrable_majorants {a : E → E → ℂ}
    (ha : ScaledJointOrderOne a) (c : SchwartzMap E ℂ) :
    ∃ M : ℕ → E → ℝ, (∀ n, Integrable (M n) (volume : Measure E)) ∧
      (∀ n e, 0 ≤ M n e) ∧ ∀ n e (p : P),
        ‖iteratedFDeriv ℝ n (coefficientTaylorIntegrand a c e) p‖ ≤ M n e / W p.2 := by
  let F := SchwartzMap.fourierTransformCLM ℂ c
  let Y (n : ℕ) (e : E) := (W e)^(n+3) * ‖F e‖
  have hY (n : ℕ) : Integrable (Y n) (volume : Measure E) := integrable_schwartz_weighted F (n+3)
  choose C hC hB using fun n : ℕ => coefficientTaylorIntegrand_order_minus_one ha c n
  let M (n : ℕ) (e : E) := C n * Y n e
  refine ⟨M,fun n => (hY n).const_mul (C n),fun n e => ?_,fun n e p => ?_⟩
  · exact mul_nonneg (hC n)
      (mul_nonneg (pow_nonneg (radian_frequency_weight_pos e).le _) (norm_nonneg _))
  · exact hB n e p

end Burnett.V03
