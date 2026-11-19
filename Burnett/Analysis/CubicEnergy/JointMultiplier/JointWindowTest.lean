import Burnett.Analysis.CubicEnergy.JointMultiplier.JointTrilinearFourier
import Burnett.Analysis.ShiftedFourierWindow.LowPassFourier

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open Burnett.Analysis.ShiftedFourierWindow
open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

private theorem dilated_temp (a : SchwartzMap E ℂ) (s : ℝ) :
    (fun z : E => a (s • z)).HasTemperateGrowth := by
  by_cases hz : s=0
  · simp only [hz,zero_smul]
    exact Function.HasTemperateGrowth.const _
  · let L := (LinearEquiv.smulOfNeZero (K := ℝ) (M := E) s hz).toContinuousLinearEquiv
    exact (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L a).hasTemperateGrowth

/-- Frequency cutoff at scale s as an actual Schwartz test. -/
def windowTest (a f : SchwartzMap E ℂ) (s : ℝ) : SchwartzMap E ℂ :=
  (SchwartzMap.fourierTransformCLE ℂ).symm
    (SchwartzMap.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) (dilated_temp a s)
      (SchwartzMap.fourierTransformCLE ℂ f))

theorem windowTest_fourier (a f : SchwartzMap E ℂ) (s : ℝ) (z : E) :
    𝓕 (windowTest a f s : E → ℂ) z = 𝓕 (f : E → ℂ) z * a (s • z) := by
  exact congrArg (fun k : SchwartzMap E ℂ => k z) ((SchwartzMap.fourierTransformCLE ℂ).apply_symm_apply _)

private def winWave (t : ℝ) : ℂ := Complex.exp ((↑(2*Real.pi*t) : ℂ)*Complex.I)
private theorem winWave_add (t u : ℝ) : winWave (t+u) = winWave t * winWave u := by
  unfold winWave
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Translating the filtered function in space gives the signed modulation
used by the square and maximal estimates. The ratio tracks the two dilations. -/
theorem windowTest_translate (a f : SchwartzMap E ℂ) (t s : ℝ) (ht : 0<t) (x y : E) :
    windowTest a f t (x-s • y) = shiftedWindowOperator a f t ((-s/t) • y) x := by
  let g := windowTest a f t
  have hrec := congrFun (g.continuous.fourier_inversion g.integrable
    (SchwartzMap.fourierTransformCLM ℂ g).integrable) (x-s • y)
  change g (x-s • y) = _
  rw [← hrec,Real.fourierIntegralInv_eq']
  apply integral_congr_ae
  filter_upwards with ξ
  change winWave (inner ℝ ξ (x-s • y))*𝓕 (windowTest a f t : E → ℂ) ξ =
    (winWave (inner ℝ ξ x)*winWave (inner ℝ (t • ξ) ((-s/t) • y))*a (t • ξ))*𝓕 (f : E → ℂ) ξ
  rw [windowTest_fourier,inner_sub_right,real_inner_smul_right,real_inner_smul_left,real_inner_smul_right]
  have sc : t*((-s/t)*inner ℝ ξ y) = -(s*inner ℝ ξ y) := by field_simp
  rw [sc,sub_eq_add_neg,winWave_add]
  ring

end Burnett.A02.FrequencySplit
