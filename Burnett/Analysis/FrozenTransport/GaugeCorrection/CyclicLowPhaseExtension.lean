import Burnett.Analysis.CubicEnergy.FrequencySplit

set_option autoImplicit false
set_option maxRecDepth 3500
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.V08

open MeasureTheory Set
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff Interval

/-- The normalized odd test factor on the independent low and high
angular variables, extended to the zero frequency ratio. -/
def cyclicLowNormalizedPhase (a : E → ℝ) (lowDir z θ : E) : ℝ :=
  a lowDir - ∫ t in (0 : ℝ)..1, fderiv ℝ a (θ + t • z) lowDir

/-- The exact cyclic test sum on the signed triad `p+q+r=0`. -/
def signedCyclicPhase (a : E → ℝ) (p q : E) : ℝ :=
  a p + a q + a (-(p + q))

/-- On the actual low-frequency region the formula agrees with the ratio
in the paper. The integration path stays away from the singular origin
even when the independent ratio variable is zero. -/
theorem signedCyclicPhase_div_eq_lowNormalized
    (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0})
    (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ (s : ℝ), 0 < s → ∀ ξ, a (s • ξ) = s * a ξ)
    (lowDir z θ : E) (hp hq : ℝ) (hp₀ : 0 < hp) (hq₀ : 0 < hq)
    (hθ : ‖θ‖ = 1) (hsmall : ‖z‖ < 1/2) (hz : z = (hp / hq) • lowDir) :
    signedCyclicPhase a (hp • lowDir) (hq • θ) / hp = cyclicLowNormalizedPhase a lowDir z θ := by
  let path (t : ℝ) : E := θ + t • z
  let U : Set E := {ξ | ξ ≠ 0}
  have hU : IsOpen U := isClosed_singleton.isOpen_compl
  have hPath : MapsTo path [[(0 : ℝ), 1]] U := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    change θ + t • z ≠ 0
    intro hZero
    have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
    have hSmall : ‖t • z‖ < 1 := by
      calc
        _ = |t| * ‖z‖ := by rw [norm_smul, Real.norm_eq_abs]
        _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right htAbs (norm_nonneg _)
        _ < _ := by rw [one_mul]; exact hsmall.trans (by norm_num)
    have hEq : θ = -(t • z) := eq_neg_of_add_eq_zero_left hZero
    rw [← norm_neg, ← hEq, hθ] at hSmall
    exact (lt_irrefl _ hSmall)
  have hCont : Continuous path := continuous_const.add (continuous_id.smul continuous_const)
  have hF : ContinuousOn (fun t => fderiv ℝ a (path t)) [[(0 : ℝ), 1]] :=
    (ha.continuousOn_fderiv_of_isOpen hU (by simp)).comp hCont.continuousOn hPath
  have hDer (t : ℝ) (ht : t ∈ [[(0 : ℝ), 1]]) :
      HasDerivAt (a ∘ path) (fderiv ℝ a (path t) z) t := by
    have hDiff := ((ha.differentiableOn (by simp)) (path t) (hPath ht)).differentiableAt
      (hU.mem_nhds (hPath ht))
    have hpDer : HasDerivAt path z t := by
      simpa [path] using ((hasDerivAt_id t).smul_const z).const_add θ
    exact hDiff.hasFDerivAt.comp_hasDerivAt t hpDer
  have hFtc : a (θ + z) - a θ = ∫ t in (0 : ℝ)..1, fderiv ℝ a (path t) z := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDer
      ((hF.clm_apply continuousOn_const).intervalIntegrable)]
    simp [path]
  have hDiff : a (θ + z) - a θ =
      (hp / hq) * ∫ t in (0 : ℝ)..1, fderiv ℝ a (path t) lowDir := by
    rw [hFtc, ← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t _
    calc
      (fderiv ℝ a (path t)) z = (fderiv ℝ a (path t)) ((hp / hq) • lowDir) :=
        congrArg (fderiv ℝ a (path t)) hz
      _ = _ := by rw [map_smul, smul_eq_mul]
  have hScale : hq * (hp / hq) = hp := by field_simp
  have hTriad : hp • lowDir + hq • θ = hq • (θ + z) := by
    rw [hz, smul_add, smul_smul, hScale, add_comm]
  unfold signedCyclicPhase cyclicLowNormalizedPhase
  rw [hOdd, hHom hp hp₀, hHom hq hq₀, hTriad, hHom hq hq₀]
  change (hp * a lowDir + hq * a θ - hq * a (θ + z)) / hp =
    a lowDir - ∫ t in (0 : ℝ)..1, fderiv ℝ a (path t) lowDir
  calc
    _ = a lowDir - hq * (a (θ + z) - a θ) / hp := by field_simp; ring
    _ = _ := by rw [hDiff]; field_simp

end Burnett.V08
