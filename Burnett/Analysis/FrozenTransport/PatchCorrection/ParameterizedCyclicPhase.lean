import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalGaugeA08Profile

set_option autoImplicit false
set_option maxHeartbeats 4600000
set_option maxRecDepth 4500
noncomputable section
namespace Burnett.V11

open Filter MeasureTheory Set Metric Burnett.V08 Burnett.P01
open Burnett.A02.FrequencySplit (E Joint)
open scoped ContDiff Topology Interval

def gaugePhaseWindow : Set (Joint × E) := {y | (y.2,y.1.1,y.1.2) ∈ cyclicLowProfileSet}

theorem gaugePhaseWindow_open : IsOpen gaugePhaseWindow := by
  have A : Continuous (fun x : Joint × E => ‖x.2‖) := continuous_snd.norm
  have B : Continuous (fun x : Joint × E => ‖x.1.1‖) := (continuous_fst.comp continuous_fst).norm
  have C : Continuous (fun x : Joint × E => ‖x.1.2‖) := (continuous_snd.comp continuous_fst).norm
  exact (isOpen_lt continuous_const A).inter ((isOpen_lt B continuous_const).inter (isOpen_lt continuous_const C))

/-- Smoothness in the frozen center and in every independent angular argument,
including ratio zero. The frequency derivative in the segment keeps its center. -/
theorem parametric_cyclicLowNormalizedPhase (a : Joint → ℝ)
    (ha : ContDiffOn ℝ ∞ a {x : Joint | x.2 ≠ 0}) :
    ContDiffOn ℝ ∞ (fun x : E × (Joint × E) => cyclicLowNormalizedPhase (fun y => a (x.1,y)) x.2.2 x.2.1.1 x.2.1.2)
      (univ ×ˢ gaugePhaseWindow) := by
  let b (x : Joint) := gaugeProjectionInfrared (8*‖x.2‖)*a x
  have hOpen : IsOpen {x : Joint | x.2 ≠ 0} := isOpen_ne_fun continuous_snd continuous_const
  have hb : ContDiff ℝ ∞ b := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x.2=0
    · apply (contDiffAt_const (c:=(0:ℝ))).congr_of_eventuallyEq
      have hn := (isOpen_lt (f:=fun p : Joint => ‖p.2‖) continuous_snd.norm (continuous_const (y:=(1/8:ℝ)))).mem_nhds
        (show ‖x.2‖ < 1/8 by rw [hx,norm_zero]; norm_num)
      filter_upwards [hn] with p hp
      change ‖p.2‖<1/8 at hp
      simp only [b,gaugeProjectionInfrared_zero (show 8*‖p.2‖ ≤ 1 by linarith),zero_mul]
    · exact (gaugeProjectionInfrared_contDiff.contDiffAt.comp x
        (contDiffAt_const.mul (contDiffAt_snd.norm ℝ hx))).mul (ha.contDiffAt (hOpen.mem_nhds hx))
  have hgerm (c : E) {y : E} (hy : 1/4 < ‖y‖) : (fun z => b (c,z)) =ᶠ[𝓝 y] (fun z => a (c,z)) := by
    filter_upwards [(isOpen_lt (f:=fun _ : E => (1/4:ℝ)) continuous_const continuous_norm).mem_nhds hy] with z hz
    change 1/4 < ‖z‖ at hz
    simp only [b,gaugeProjectionInfrared_one (show 2 ≤ 8*‖z‖ by linarith),one_mul]
  let L := ContinuousLinearMap.inr ℝ E E
  have hslice (x y : E) : fderiv ℝ (fun t => b (x,t)) y = (fderiv ℝ b (x,y)).comp L := by
    have incl : HasFDerivAt (fun t : E => (x,t)) L y := (hasFDerivAt_const x y).prodMk (hasFDerivAt_id y)
    exact ((hb.differentiable (by simp)).differentiableAt.hasFDerivAt.comp y incl).fderiv
  let F (p : (E × (Joint × E)) × ℝ) := fderiv ℝ b (p.1.1, p.1.2.1.2 + p.2 • p.1.2.1.1) (0,p.1.2.2)
  have hF : ContDiff ℝ ∞ F := by
    dsimp only [F]
    apply ((hb.fderiv_right (by simp)).comp ?_).clm_apply
    · fun_prop
    · fun_prop
  have smooth : ContDiff ℝ ∞ (fun p : E × (Joint × E) => b (p.1,p.2.2) - ∫ t in (0:ℝ)..1, F (p,t)) :=
    (hb.comp (contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd))).sub (contDiff_unitIntervalIntegral F hF)
  apply smooth.contDiffOn.congr
  intro x hx
  obtain ⟨hlo,hr,hh⟩ := hx.2
  unfold cyclicLowNormalizedPhase
  rw [(hgerm x.1 hlo).eq_of_nhds]
  congr 1
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le zero_le_one] at ht
  have habs : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  have hz : ‖t • x.2.1.1‖ ≤ ‖x.2.1.1‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right habs (norm_nonneg _)).trans_eq (one_mul _)
  have triangle : ‖x.2.1.2‖ ≤ ‖x.2.1.2+t • x.2.1.1‖ + ‖t • x.2.1.1‖ := by
    have h := norm_add_le (x.2.1.2+t • x.2.1.1) (-(t • x.2.1.1))
    simpa only [add_neg_cancel_right,norm_neg] using h
  have away : 1/4 < ‖x.2.1.2+t • x.2.1.1‖ := by linarith
  let s := x.2.1.2+t • x.2.1.1
  change fderiv ℝ (fun z => a (x.1,z)) s x.2.2 = fderiv ℝ b (x.1,s) (0,x.2.2)
  calc
    _ = fderiv ℝ (fun z => b (x.1,z)) s x.2.2 := by rw [(hgerm x.1 away).fderiv_eq]
    _ = _ := by rw [hslice]; rfl

end Burnett.V11
