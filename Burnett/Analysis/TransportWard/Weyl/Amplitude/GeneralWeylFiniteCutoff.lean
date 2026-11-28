import Burnett.Analysis.CubicEnergy.BilinearMultiplier.RadianFrequency

set_option autoImplicit false
set_option maxHeartbeats 5700000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff FourierTransform ENNReal Topology

/-- A smooth compact frequency cutoff can be applied in the same normalized
frequency used by the manuscript-radian midpoint integral. -/
def generalWeylCutoffProfile (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (χS : HasCompactSupport χ)
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b) : SchwartzMap E ℂ := by
  let B (ξ : E) := b (tau • ξ)
  have scale : ContDiff ℝ ∞ (fun ξ : E => tau • ξ) := contDiff_const.smul contDiff_id
  have hb' : ContDiff ℝ ∞ B := hb.comp scale
  have support : HasCompactSupport (χ * B) := χS.mul_right
  exact (support.comp_left Complex.ofReal_zero).toSchwartzMap (Complex.ofRealCLM.contDiff.comp (hχ.mul hb'))

theorem general_weyl_cutoff_profile_apply (χ : E → ℝ) (hχ : ContDiff ℝ ∞ χ) (χS : HasCompactSupport χ)
    (b : E → ℝ) (hb : ContDiff ℝ ∞ b) (ξ : E) :
    generalWeylCutoffProfile χ hχ χS b hb ξ = (χ ξ * b (tau • ξ) : ℝ) := rfl

end Burnett.A03
