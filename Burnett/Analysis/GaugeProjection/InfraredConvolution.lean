import Burnett.Analysis.GaugeProjection.GaugeProjectionLp
import Burnett.Analysis.Fourier.RadianCoordinateDerivative
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest

set_option autoImplicit false
set_option maxHeartbeats 2200000

noncomputable section

namespace Burnett.P01

open Set Filter MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A07 (coordinateDerivative)
open Burnett.Analysis.ShiftedFourierWindow (shifted_window_physical)
open scoped FourierTransform ContDiff Topology

private theorem tau_pos : 0 < tau := mul_pos (by norm_num) Real.pi_pos

private def projectionLowSymbol (ν : E) : ℂ :=
  ((1 - gaugeProjectionInfrared (tau * ‖ν‖) : ℝ) : ℂ)

private theorem projectionLowSymbol_smooth : ContDiff ℝ ∞ projectionLowSymbol := by
  rw [contDiff_iff_contDiffAt]
  intro ν
  by_cases hν : ν = 0
  · subst ν
    have hnear : {x : E | tau * ‖x‖ < 1} ∈ 𝓝 (0 : E) :=
      (isOpen_lt (continuous_const.mul continuous_norm) continuous_const).mem_nhds
        (by simp)
    refine (contDiffAt_const (c := (1 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [hnear] with x hx
    simp [projectionLowSymbol, gaugeProjectionInfrared_zero hx.le]
  · exact Complex.ofRealCLM.contDiff.contDiffAt.comp ν
      (contDiffAt_const.sub <| gaugeProjectionInfrared_contDiff.contDiffAt.comp ν <|
        contDiffAt_const.mul (contDiffAt_id.norm ℝ hν))

private theorem projectionLowSymbol_compact : HasCompactSupport projectionLowSymbol := by
  have hsupport : Function.support projectionLowSymbol ⊆ Metric.closedBall (0 : E) (2 / tau) := by
    intro ν hν
    by_contra h
    rw [mem_closedBall_zero_iff] at h
    have hlarge : 2 ≤ tau * ‖ν‖ := by
      have he := ((div_lt_iff₀ tau_pos).mp (lt_of_not_ge h)).le
      simpa only [mul_comm] using he
    exact hν (by simp [projectionLowSymbol, gaugeProjectionInfrared_one hlarge])
  exact (isCompact_closedBall (0 : E) (2 / tau)).of_isClosed_subset isClosed_closure
    (closure_minimal hsupport Metric.isClosed_closedBall)

/-- The low complement of the fixed infrared cutoff, in the normalized
Fourier coordinates of mathlib. -/
def projectionLowProfile : SchwartzMap E ℂ :=
  projectionLowSymbol_compact.toSchwartzMap projectionLowSymbol_smooth

/-- The actual inverse transform of the fixed low-frequency complement. -/
def projectionLowKernel : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm projectionLowProfile

private theorem projectionInfraredAction_sub_low (w : SchwartzMap E ℂ) :
    projectionInfraredAction w = w - windowTest projectionLowProfile w 1 := by
  apply (SchwartzMap.fourierTransformCLE ℂ).injective
  ext ν
  rw [map_sub, SchwartzMap.sub_apply]
  change 𝓕 (projectionInfraredAction w : E → ℂ) ν =
    𝓕 (w : E → ℂ) ν - 𝓕 (windowTest projectionLowProfile w 1 : E → ℂ) ν
  rw [← radianFourier_scaled (projectionInfraredAction w : E → ℂ),
    radianFourier_projectionInfraredAction, radianFourier_scaled, windowTest_fourier, one_smul,
    norm_smul, Real.norm_of_nonneg tau_pos.le]
  change _ = _ - _ * ((1 - gaugeProjectionInfrared (tau * ‖ν‖) : ℝ) : ℂ)
  push_cast
  ring

/-- The same fixed infrared action, written as identity minus convolution.
The formula also gives its action on individual functions whenever the
integral exists. -/
def projectionInfraredKernelAction (w : E → ℂ) (x : E) : ℂ :=
  w x - ∫ y, projectionLowKernel (x - y) * w y

theorem projectionInfraredAction_eq_kernel (w : SchwartzMap E ℂ) (x : E) :
    projectionInfraredAction w x = projectionInfraredKernelAction w x := by
  rw [projectionInfraredAction_sub_low, SchwartzMap.sub_apply, projectionInfraredKernelAction]
  congr 1
  have h := windowTest_translate projectionLowProfile w 1 1 one_pos x 0
  rw [shifted_window_physical projectionLowProfile w 1 one_pos] at h
  simpa [projectionLowKernel] using h

/-- The convolution envelope furnished by the first moment of the kernel derivative. -/
def projectionLowMoment (b : Fin 4) (z : E) : ℝ :=
  ‖z‖ * ‖coordinateDerivative b projectionLowKernel z‖ + ‖projectionLowKernel z‖

theorem projectionLowMoment_integrable (b : Fin 4) : Integrable (projectionLowMoment b) := by
  have i := (coordinateDerivative b projectionLowKernel).integrable_pow_mul volume 1
  simpa only [pow_one, projectionLowMoment] using i.add projectionLowKernel.integrable.norm

end Burnett.P01
