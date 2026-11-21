import Burnett.Analysis.CubicEnergy.CompleteEnergy.QuasilinearIBP
import Burnett.Analysis.ShiftedFourierWindow.LowPassLp

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open Burnett.Analysis.CenteredMaximal (maximalConstant maximalConstant_finite)
open MeasureTheory
open scoped ENNReal FourierTransform RealInnerProductSpace

/-- Apply a fixed Schwartz frequency profile in mathlib's Fourier variables. -/
def fixedSchwartzFourierAction (a f : SchwartzMap E ℂ) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm (energyProduct a (SchwartzMap.fourierTransformCLE ℂ f))

theorem fixedSchwartzFourierAction_spectrum (a f : SchwartzMap E ℂ) (ξ : E) :
    𝓕 (fixedSchwartzFourierAction a f : E → ℂ) ξ = a ξ * 𝓕 (f : E → ℂ) ξ := by
  change ((SchwartzMap.fourierTransformCLE ℂ) ((SchwartzMap.fourierTransformCLE ℂ).symm
    (energyProduct a (SchwartzMap.fourierTransformCLE ℂ f)))) ξ = _
  rw [(SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply]
  rfl

theorem fixedSchwartzFourierAction_inverse (a f : SchwartzMap E ℂ) :
    (fixedSchwartzFourierAction a f : E → ℂ) = 𝓕⁻ (fun ξ => a ξ * 𝓕 (f : E → ℂ) ξ) := by
  let F := energyProduct a (SchwartzMap.fourierTransformCLE ℂ f)
  change ((SchwartzMap.fourierTransformCLE ℂ).symm F : E → ℂ) = _
  have h : ((SchwartzMap.fourierTransformCLE ℂ).symm F : E → ℂ) = 𝓕⁻ (F : E → ℂ) :=
    SchwartzMap.fourierTransformCLE_symm_apply _ _
  rw [h]
  rfl

theorem fixedSchwartzFourierAction_shifted (a f : SchwartzMap E ℂ) (x : E) :
    fixedSchwartzFourierAction a f x = shiftedWindowOperator a f 1 0 x := by
  rw [fixedSchwartzFourierAction_inverse, Real.fourierIntegralInv_eq']
  unfold shiftedWindowOperator
  apply integral_congr_ae
  filter_upwards with ξ
  let w : ℂ := Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
  change w * (a ξ * 𝓕 (f : E → ℂ) ξ) =
    (w * Complex.exp ((↑(2 * Real.pi * inner ℝ ((1 : ℝ) • ξ) (0 : E)) : ℂ) * Complex.I) *
      a ((1 : ℝ) • ξ)) * 𝓕 (f : E → ℂ) ξ
  simp [mul_assoc]

/-- The same physical multiplier is convolution with the actual inverse profile. -/
theorem fixedSchwartzFourierAction_convolution (a f : SchwartzMap E ℂ) (x : E) :
    fixedSchwartzFourierAction a f x =
      ∫ y, ((SchwartzMap.fourierTransformCLE ℂ).symm a) (x - y) * f y := by
  rw [fixedSchwartzFourierAction_shifted]
  simpa using shifted_window_physical a f 1 (by norm_num) 0 x

/-- A fixed profile supplies an Lᵖ bound before the Schwartz input is selected. -/
theorem fixedSchwartzFourierAction_Lp (a : SchwartzMap E ℂ) (p : ℝ) (hp : 1 < p) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ f : SchwartzMap E ℂ,
      eLpNorm (fixedSchwartzFourierAction a f : E → ℂ) (ENNReal.ofReal p) volume ≤
        C * eLpNorm (f : E → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨C, hC, bound⟩ := maximalShiftedWindow_Lp a
  have hfin := ENNReal.rpow_lt_top_of_nonneg
    (one_div_nonneg.mpr (zero_le_one.trans hp.le)) (maximalConstant_finite p).ne
  refine ⟨C * maximalConstant p ^ (1 / p), ENNReal.mul_lt_top hC hfin, ?_⟩
  intro f
  have dom (x : E) : ‖fixedSchwartzFourierAction a f x‖ₑ ≤ maximalShiftedWindow a f 0 x := by
    rw [fixedSchwartzFourierAction_shifted]
    exact le_iSup (fun s : {t : ℝ // 0 < t} => ‖shiftedWindowOperator a f s 0 x‖ₑ)
      ⟨1, by norm_num⟩
  exact (eLpNorm_mono_enorm dom).trans (by simpa using bound f 0 p hp)

end Burnett.A02.FrequencySplit
