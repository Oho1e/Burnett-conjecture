import Burnett.Analysis.FrozenTransport.GaugeCorrection.CompactParameterIntegral
import Burnett.Analysis.FrozenTransport.GaugeCorrection.CyclicLowPhaseExtension
import Burnett.Analysis.GaugeProjection.GaugeProjectionSymbol

set_option autoImplicit false
set_option maxRecDepth 4300
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.V08

open Filter MeasureTheory Metric Set Burnett.P01
open Burnett.A02.FrequencySplit (E)
open scoped ContDiff Interval Topology

/-- An open domain containing the unit low and high angles, with the
low/high ratio allowed to pass through zero. -/
def cyclicLowProfileSet : Set (E × E × E) :=
  {x | 1/4 < ‖x.1‖ ∧ ‖x.2.1‖ < 1/2 ∧ 3/4 < ‖x.2.2‖}

private def phaseTestOutsideOrigin (a : E → ℝ) (ξ : E) : ℝ :=
  gaugeProjectionInfrared (8 * ‖ξ‖) * a ξ

private theorem phaseTestOutsideOrigin_contDiff (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) :
    ContDiff ℝ ∞ (phaseTestOutsideOrigin a) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ξ = 0
  · subst ξ
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [ball_mem_nhds (0 : E) (by norm_num : (0 : ℝ) < 1 / 8)] with y hy
    have hn : ‖y‖ < 1/8 := mem_ball_zero_iff.mp hy
    simp only [phaseTestOutsideOrigin, gaugeProjectionInfrared_zero (by linarith : 8 * ‖y‖ ≤ 1), zero_mul]
  · have hU : IsOpen {ξ : E | ξ ≠ 0} := isClosed_singleton.isOpen_compl
    have hA : ContDiffAt ℝ ∞ a ξ := ha.contDiffAt (hU.mem_nhds hξ)
    exact (gaugeProjectionInfrared_contDiff.contDiffAt.comp ξ
      (contDiffAt_const.mul (contDiffAt_id.norm ℝ hξ))).mul hA

private theorem phaseTestOutsideOrigin_germ (a : E → ℝ) {ξ : E} (hξ : 1/4 < ‖ξ‖) :
    phaseTestOutsideOrigin a =ᶠ[𝓝 ξ] a := by
  have hN := (isOpen_lt (f := fun _ : E => (1/4 : ℝ)) continuous_const continuous_norm).mem_nhds hξ
  filter_upwards [hN] with y hy
  change 1/4 < ‖y‖ at hy
  simp only [phaseTestOutsideOrigin, gaugeProjectionInfrared_one (by linarith : 2 ≤ 8 * ‖y‖), one_mul]

/-- The exact normalized cyclic test has all joint derivatives down to
zero ratio. The derivative in the integral sees the original test's germ
along the entire segment. -/
theorem cyclicLowNormalizedPhase_contDiffOn (a : E → ℝ) (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) :
    ContDiffOn ℝ ∞ (fun x : E × E × E => cyclicLowNormalizedPhase a x.1 x.2.1 x.2.2)
      cyclicLowProfileSet := by
  let b := phaseTestOutsideOrigin a
  have hb : ContDiff ℝ ∞ b := phaseTestOutsideOrigin_contDiff a ha
  let F (p : (E × E × E) × ℝ) : ℝ := (fderiv ℝ b (p.1.2.2 + p.2 • p.1.2.1)) p.1.1
  have hF : ContDiff ℝ ∞ F := by
    have hz : ContDiff ℝ ∞ (fun p : (E × E × E) × ℝ => p.1.2.1) :=
      contDiff_fst.comp (contDiff_snd.comp contDiff_fst)
    have hθ : ContDiff ℝ ∞ (fun p : (E × E × E) × ℝ => p.1.2.2) :=
      contDiff_snd.comp (contDiff_snd.comp contDiff_fst)
    exact ((hb.fderiv_right (by simp)).comp (hθ.add (contDiff_snd.smul hz))).clm_apply
      (contDiff_fst.comp contDiff_fst)
  have hSmooth : ContDiff ℝ ∞
      (fun x : E × E × E => cyclicLowNormalizedPhase b x.1 x.2.1 x.2.2) :=
    (hb.comp contDiff_fst).sub (contDiff_unitIntervalIntegral F hF)
  apply hSmooth.contDiffOn.congr
  intro x hx
  obtain ⟨hLow, hRatio, hHigh⟩ := hx
  unfold cyclicLowNormalizedPhase
  have hPoint : b x.1 = a x.1 := (phaseTestOutsideOrigin_germ a hLow).eq_of_nhds
  rw [hPoint]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have htAbs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hz : ‖t • x.2.1‖ ≤ ‖x.2.1‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right htAbs (norm_nonneg _)).trans_eq (one_mul _)
  have hTriangle : ‖x.2.2‖ ≤ ‖x.2.2 + t • x.2.1‖ + ‖t • x.2.1‖ := by
    have h := norm_add_le (x.2.2 + t • x.2.1) (-(t • x.2.1))
    simpa only [add_neg_cancel_right, norm_neg] using h
  have hAway : 1/4 < ‖x.2.2 + t • x.2.1‖ := by linarith
  have hDerivative : fderiv ℝ b (x.2.2 + t • x.2.1) = fderiv ℝ a (x.2.2 + t • x.2.1) :=
    (phaseTestOutsideOrigin_germ a hAway).fderiv_eq
  exact (congrArg (fun L : E →L[ℝ] ℝ => L x.1) hDerivative).symm

end Burnett.V08
