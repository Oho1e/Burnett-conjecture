import Burnett.Analysis.CubicEnergy.AngularCorrection.RadianCoordinateQuotient
import Burnett.Analysis.Fourier.FixedInfraredSchwartz
import Burnett.Analysis.CubicEnergy.JointMultiplier.JointWindowTest
import Burnett.Analysis.ShiftedFourierWindow.LowPassLp

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.A07

open Filter Set Metric MeasureTheory
open Burnett.A02.FrequencySplit (E Joint radianFourier radianFourier_scaled tau windowTest
  windowTest_fourier windowTest_translate)
open Burnett.A06 (radianHighPair radianHighPairWeight)
open Burnett.Analysis.CenteredMaximal (maximalConstant maximalConstant_finite)
open Burnett.Analysis.ShiftedFourierWindow
open scoped Topology ContDiff FourierTransform ENNReal ComplexConjugate

/-- A high-input radial cutoff can be supplied by filtering the original high
Schwartz field. The bilinear symbol and all other factors stay the same. -/
theorem radianHighPair_fixedInfrared_on_input
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (r R : ℝ) (hr : 0 < r)
    (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1)
    (q : Joint → ℂ) (f u w : SchwartzMap E ℂ) :
    radianHighPair (fun x => η ‖x.2‖ • q x) f u w =
      radianHighPair q f (fixedInfraredSchwartz η hη r R hr hzero hone u) w := by
  unfold radianHighPair
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianHighPairWeight, fixedInfraredSchwartz_radianFourier, Complex.real_smul]
  ring

/-- For the high adjoint the original infrared cutoff acts on the output.
Its reality moves it to the same Fourier window on the Schwartz test. -/
theorem radianHighPair_fixedInfrared_on_output
    (η : ℝ → ℝ) (hη : ContDiff ℝ ∞ η) (r R : ℝ) (hr : 0 < r)
    (hzero : ∀ s ≤ r, η s = 0) (hone : ∀ s ≥ R, η s = 1)
    (q : Joint → ℂ) (f u w : SchwartzMap E ℂ) :
    radianHighPair (fun x => η ‖x.2+x.1‖ • q x) f u w =
      radianHighPair q f u (fixedInfraredSchwartz η hη r R hr hzero hone w) := by
  unfold radianHighPair
  congr 1
  apply integral_congr_ae
  filter_upwards with p
  simp only [radianHighPairWeight, fixedInfraredSchwartz_radianFourier, Complex.real_smul,
    map_mul, Complex.conj_ofReal]
  ring

end Burnett.A07
