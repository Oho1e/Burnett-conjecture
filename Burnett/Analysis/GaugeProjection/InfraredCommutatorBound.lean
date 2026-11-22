import Burnett.Analysis.GaugeProjection.InfraredCommutator
import Burnett.Analysis.PrincipalEnergy.Quantization.ConvolutionEnvelope

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.P01

open MeasureTheory
open Burnett.A02.FrequencySplit (E)
open Burnett.A07 (coordinateDerivative)
open Burnett.Analysis.FirstOrderDyadic (convolution_envelope_action_norm_le)
open scoped BigOperators NNReal

/-- The absolute first-moment mass of the fixed cutoff kernel derivative and
the mass of the fixed cutoff kernel, summed over the four directions. -/
def projectionInfraredCommutatorConstant : ℝ :=
  ∑ b : Fin 4, ∫ z, projectionLowMoment b z

private theorem projectionLowMoment_nonneg (b : Fin 4) (z : E) :
    0 ≤ projectionLowMoment b z := by unfold projectionLowMoment; positivity

theorem projectionInfraredCommutatorConstant_nonneg :
    0 ≤ projectionInfraredCommutatorConstant :=
  Finset.sum_nonneg fun b _ => integral_nonneg (projectionLowMoment_nonneg b)

/-- The true reduced kernel is an \(L^2\) operator with the uniform gradient
bound for the original fixed infrared cutoff. -/
theorem projectionInfraredCommutatorKernel_l2 (b : Fin 4) (f : E → ℂ) (L : ℝ≥0)
    (hf : ContDiff ℝ 1 f) (hL : LipschitzWith L f) (u : E → ℂ)
    (hu : Measurable u) (hu1 : Integrable u) (hu2 : MemLp u 2 volume) :
    ∃ h : MemLp (fun x => ∫ y, projectionInfraredCommutatorKernel b f x y * u y) 2 volume,
      ‖h.toLp (fun x => ∫ y, projectionInfraredCommutatorKernel b f x y * u y)‖ ≤
        (L : ℝ) * projectionInfraredCommutatorConstant * ‖hu2.toLp u‖ := by
  have hM : Measurable (projectionLowMoment b) := by
    have hK := projectionLowKernel.continuous
    have hDK := (coordinateDerivative b projectionLowKernel).continuous
    unfold projectionLowMoment
    fun_prop
  obtain ⟨ha, bound⟩ := convolution_envelope_action_norm_le (projectionInfraredCommutatorKernel b f)
    (projectionInfraredCommutatorKernel_continuous b f hf).measurable
    (fun z => (L : ℝ) * projectionLowMoment b z) (measurable_const.mul hM)
    (fun z => mul_nonneg L.2 (projectionLowMoment_nonneg b z))
    ((projectionLowMoment_integrable b).const_mul (L : ℝ))
    (norm_projectionInfraredCommutatorKernel_le b f L hL) u hu hu1 hu2
  have hsum : (∫ z, projectionLowMoment b z) ≤ projectionInfraredCommutatorConstant :=
    Finset.single_le_sum (f := fun j : Fin 4 => ∫ z, projectionLowMoment j z)
      (fun j _ => integral_nonneg (projectionLowMoment_nonneg j)) (Finset.mem_univ b)
  refine ⟨ha, bound.trans ?_⟩
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum L.2) (norm_nonneg _)

/-- The fixed infrared commutator on the original differentiated Schwartz
input, with any globally Lipschitz C¹ coefficient. -/
theorem projectionInfraredKernelAction_commutator_l2 (b : Fin 4) (f : E → ℂ) (L : ℝ≥0)
    (hf : ContDiff ℝ 1 f) (hL : LipschitzWith L f) (w : SchwartzMap E ℂ) :
    let v := fun x =>
      projectionInfraredKernelAction (fun y => f y * coordinateDerivative b w y) x -
        f x * projectionInfraredKernelAction (coordinateDerivative b w) x
    ∃ h : MemLp v 2 volume,
      ‖h.toLp v‖ ≤ (L : ℝ) * projectionInfraredCommutatorConstant * ‖w.toLp 2 volume‖ := by
  intro v
  have eq : v = fun x => ∫ y, projectionInfraredCommutatorKernel b f x y * w y :=
    funext (projectionInfraredKernelAction_commutator_derivative b f L hf hL w)
  rw [eq]
  exact projectionInfraredCommutatorKernel_l2 b f L hf hL w w.continuous.measurable
    w.integrable (w.memLp 2 volume)

end Burnett.P01
