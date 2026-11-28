import Burnett.Analysis.TransportWard.Weyl.Amplitude.DyadicWeylFinite

set_option autoImplicit false
set_option maxHeartbeats 4900000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.RicciSymbol Burnett.Analysis.FirstOrderDyadic
open Burnett.A02.FrequencySplit (E)
open Burnett.Microlocal.AngularDyadicKernel
  (radialCore radialCore_eq_zero radialCore_contDiff radialCore_eq_one radialCore_nonneg radialCore_le_one dyadicScale)
open scoped ContDiff ENNReal Topology BigOperators

private theorem dyadic_weyl_cutoff_smooth (n : ℕ) : ContDiff ℝ ∞ (dyadicWeylCutoff n) := by
  have scale : ContDiff ℝ ∞ (fun ξ : E => (dyadicScale n)⁻¹ • ξ) := contDiff_const.smul contDiff_id
  exact radialCore_contDiff.comp scale

private theorem dyadic_weyl_cutoff_supported (n : ℕ) : HasCompactSupport (dyadicWeylCutoff n) := by
  have sn : 0 < dyadicScale n := by unfold dyadicScale; positivity
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2 * dyadicScale n))
  intro ξ hξ
  by_contra! far
  have hR : 2 * dyadicScale n < ‖ξ‖ := by simpa only [mem_closedBall, dist_zero_right, not_le] using far
  have near : 2 ≤ ‖(dyadicScale n)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr sn.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ sn).mpr hR.le
  exact hξ (radialCore_eq_zero _ near)

private theorem dyadic_weyl_cutoff_norm_le_one (n : ℕ) (ξ : E) : ‖dyadicWeylCutoff n ξ‖ ≤ 1 := by
  rw [dyadicWeylCutoff, Real.norm_of_nonneg (radialCore_nonneg _)]
  exact radialCore_le_one _

end Burnett.A03
