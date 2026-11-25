import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.LeftRightNhds

/-! The two auxiliary limits in the original transport estimate. -/
set_option autoImplicit false

noncomputable section

namespace Burnett.C04

open Filter Set
open scoped Topology

private theorem eventually_pos_lt_rightZero {b : ℝ} (hb : 0 < b) :
    ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x ∧ x < b :=
  eventually_mem_nhdsWithin.and (nhdsWithin_le_nhds (Iio_mem_nhds hb))

/-- Once the fixed-parameter sequence limit gives the paper's bound, first
send the spatial scale to zero at fixed angle. The angle limit then forces
the same residual to vanish. The spatial constants may depend on the angle. -/
theorem residual_eq_zero_of_two_scale_bound
    (I C α β δ₀ : ℝ) (hα : 0 < α) (hβ : 0 < β) (hδ₀ : 0 < δ₀)
    (hEstimate : ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ D E ℓ₀ : ℝ, 0 < ℓ₀ ∧
      ∀ ℓ : ℝ, 0 < ℓ → ℓ < ℓ₀ → |4 * I| ≤ C * δ ^ β + D * ℓ ^ α + E * ℓ) : I = 0 := by
  have hAtFixedAngle (δ : ℝ) (hδ : 0 < δ) (hδHi : δ < δ₀) : |4 * I| ≤ C * δ ^ β := by
    obtain ⟨D, E, ℓ₀, hℓ₀, hBound⟩ := hEstimate δ hδ hδHi
    have hPow := Real.continuousAt_rpow_const (0 : ℝ) α (Or.inr hα.le)
    have hTail : ContinuousAt (fun ℓ : ℝ => C * δ ^ β + D * ℓ ^ α + E * ℓ) 0 :=
      (continuousAt_const.add (continuousAt_const.mul hPow)).add (continuousAt_const.mul continuousAt_id)
    have hT : Tendsto (fun ℓ : ℝ => C * δ ^ β + D * ℓ ^ α + E * ℓ)
        (𝓝[>] 0) (𝓝 (C * δ ^ β)) := by
      simpa only [Real.zero_rpow hα.ne', mul_zero, add_zero] using hTail.tendsto.mono_left nhdsWithin_le_nhds
    apply ge_of_tendsto hT
    filter_upwards [eventually_pos_lt_rightZero hℓ₀] with ℓ hℓ
    exact hBound ℓ hℓ.1 hℓ.2
  have hPow := Real.continuousAt_rpow_const (0 : ℝ) β (Or.inr hβ.le)
  have hCont : ContinuousAt (fun δ : ℝ => C * δ ^ β) 0 := continuousAt_const.mul hPow
  have hFinal : Tendsto (fun δ : ℝ => C * δ ^ β) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hβ.ne', mul_zero] using hCont.tendsto.mono_left nhdsWithin_le_nhds
  have hZero : |4 * I| ≤ 0 := by
    apply ge_of_tendsto hFinal
    filter_upwards [eventually_pos_lt_rightZero hδ₀] with δ hδ
    exact hAtFixedAngle δ hδ.1 hδ.2
  exact (mul_eq_zero.mp (abs_eq_zero.mp (le_antisymm hZero (abs_nonneg _)))).resolve_left (by norm_num)

end Burnett.C04
