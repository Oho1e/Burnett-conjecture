import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactFrequencyKernel
import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyKernel
import Burnett.Analysis.PrincipalEnergy.Quantization.ActualDerivative
import Burnett.Analysis.PrincipalEnergy.Quantization.SourceDerivative

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section

namespace Burnett.A03

open Bornology Filter MeasureTheory Metric Set Burnett.RicciSymbol
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.FirstOrderDyadic
open Burnett.Microlocal.AngularDyadicKernel
  (radialCore radialCore_contDiff radialCore_eq_zero annulus annulus_contDiff annulus_eq_zero_far
    dyadicScale scaledSchwartz_high_bound)
open scoped ContDiff FourierTransform Topology BigOperators

private theorem a01_positive_scale (j : ℕ) : 0 < dyadicScale j := by
  unfold dyadicScale
  positivity

/-- The A01 low inverse Fourier kernel is jointly C¹. -/
theorem a01_low_frequency_kernel_contDiff (a : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry a)) :
    ContDiff ℝ 1 (fun p : E × E => firstOrderLowKernel a p.1 p.2) := by
  have support (ξ : E) (outside : ξ ∉ closedBall (0 : E) 2) : radialCore ξ = 0 := by
    apply radialCore_eq_zero
    have h : 2 < ‖ξ‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using outside
    exact h.le
  exact (compact_frequency_kernel_contDiff_and_base a radialCore 2 smooth
    (radialCore_contDiff.of_le (by simp)) support).1

/-- The A01 inverse Fourier frequency band is jointly C¹. Its base derivative
is the same actual band with the symbol differentiated in the base. -/
theorem a01_annular_kernel_contDiff_and_base (a : E → E → ℂ)
    (smooth : ContDiff ℝ 1 (Function.uncurry a)) (j : ℕ) :
    ContDiff ℝ 1 (fun p : E × E => firstOrderAnnularKernel a p.1 j p.2) ∧
    ∀ x z e : E, fderiv ℝ (fun p : E × E => firstOrderAnnularKernel a p.1 j p.2)
      (x,z) (e,0) = firstOrderAnnularKernel (baseDirectionSymbol a e) x j z := by
  let χ (ξ : E) := annulus ((dyadicScale j)⁻¹ • ξ)
  have coreD : ContDiff ℝ 1 annulus := annulus_contDiff.of_le (by simp)
  have scaleD : ContDiff ℝ 1 (fun ξ : E => (dyadicScale j)⁻¹ • ξ) := contDiff_const.smul contDiff_id
  have χD : ContDiff ℝ 1 χ := coreD.comp scaleD
  have support (ξ : E) (outside : ξ ∉ closedBall (0 : E) (4 * dyadicScale j)) : χ ξ = 0 := by
    have C : 4 * dyadicScale j < ‖ξ‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using outside
    apply annulus_eq_zero_far
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (a01_positive_scale j).le), ← div_eq_inv_mul]
    exact (le_div_iff₀ (a01_positive_scale j)).mpr C.le
  exact compact_frequency_kernel_contDiff_and_base a χ (4 * dyadicScale j) smooth χD support

end Burnett.A03
