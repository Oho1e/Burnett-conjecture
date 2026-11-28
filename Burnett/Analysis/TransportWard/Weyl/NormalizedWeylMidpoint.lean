import Burnett.Analysis.CubicEnergy.JointMultiplier.MikhlinPartition
import Burnett.Analysis.TransportWard.Weyl.OriginalWeylMidpointComparison
import Burnett.Analysis.TransportWard.Weyl.Amplitude.GeneralWeylFiniteCutoff

set_option autoImplicit false

noncomputable section

namespace Burnett.V03

open Filter Function MeasureTheory Metric Burnett.A03 Burnett.A02.FrequencySplit
open Burnett.Analysis.FirstOrderDyadic
open scoped ContDiff Topology

/-- The explicit exhausting radial cutoffs used in the spatial Fourier
Weyl series yield the actual chart Weyl action on the same input. -/
theorem windowedWeyl_normalized_midpoint_tendsto_leftAction
    (θ : E → ℝ) (β : E → E → ℂ) (R : ℝ)
    (h : CompactRadianTwoPointOrderOne (windowedWeylAmplitude θ β) R R)
    (χ : SchwartzMap E ℂ) (hχ : ∀ x, χ x = (θ x : ℂ))
    (u : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun n : ℕ => (θ x : ℂ) *
      (∫ y : E, (∫ ξ : E, patchFourierPhase ξ (x - y) *
          (mikhlinBall (((n : ℝ) + 1)⁻¹ • ξ) : ℂ) * β ((1 / 2 : ℝ) • (x + y)) (tau • ξ)) *
        scalarSchwartzProduct χ u y)) atTop
      (𝓝 (firstOrderAction (windowedWeylLeftSymbol θ β R h) u x)) := by
  let f (n : ℕ) (ξ : E) := mikhlinBall (((n : ℝ) + 1)⁻¹ • ξ)
  have fSmooth (n : ℕ) : ContDiff ℝ ∞ (f n) :=
    mikhlinBall.contDiff.comp (contDiff_const.smul contDiff_id)
  have fCompact (n : ℕ) : HasCompactSupport (f n) := by
    apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : E) (2 * ((n : ℝ) + 1)))
    intro ξ hξ
    by_contra hOutside
    have h : 2 * ((n : ℝ) + 1) < ‖ξ‖ := by
      simpa only [mem_closedBall, dist_zero_right, not_le] using hOutside
    have hFar : 2 ≤ dist (((n : ℝ) + 1)⁻¹ • ξ) (0 : E) := by
      rw [dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
      exact (le_div_iff₀ (by positivity)).mpr h.le
    exact hξ (mikhlinBall.zero_of_le_dist hFar)
  let κ (n : ℕ) : SchwartzMap E ℂ :=
    generalWeylCutoffProfile (f n) (fSmooth n) (fCompact n) (fun _ => 1) contDiff_const
  have applyκ (n : ℕ) (ξ : E) : κ n ξ = (f n ξ : ℂ) := by
    simp only [κ, general_weyl_cutoff_profile_apply, mul_one]
  have hNorm (n : ℕ) (ξ : E) : ‖κ n ξ‖ ≤ 1 := by
    rw [applyκ, Complex.norm_real, Real.norm_of_nonneg mikhlinBall.nonneg]
    exact mikhlinBall.le_one
  have hLimit (ξ : E) : Tendsto (fun n => κ n ξ) atTop (𝓝 1) := by
    obtain ⟨N, hN⟩ := exists_nat_ge ‖ξ‖
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have h : ‖ξ‖ ≤ (n : ℝ) + 1 :=
      hN.trans ((Nat.cast_le.mpr hn).trans (le_add_of_nonneg_right zero_le_one))
    have hInside : (((n : ℝ) + 1)⁻¹ • ξ) ∈ closedBall (0 : E) 1 := by
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (by positivity), ← div_eq_inv_mul]
      exact (div_le_iff₀ (by positivity)).mpr (by simpa only [one_mul] using h)
    rw [applyκ]
    change (1 : ℂ) = (mikhlinBall (((n : ℝ) + 1)⁻¹ • ξ) : ℂ)
    rw [mikhlinBall.one_of_mem_closedBall hInside, Complex.ofReal_one]
  simpa only [radianMidpointWithCutoff, applyκ, f] using
    windowedWeyl_midpoint_tendsto_leftAction θ β R h χ hχ κ hNorm hLimit u x

end Burnett.V03
