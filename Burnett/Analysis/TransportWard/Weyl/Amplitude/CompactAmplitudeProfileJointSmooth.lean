import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactAmplitudeActualFourierJets
import Burnett.Analysis.TransportWard.Weyl.Amplitude.CompactSupportParameterIntegral

set_option autoImplicit false
set_option maxHeartbeats 5300000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Metric Set Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal Topology RealInnerProductSpace

private abbrev WholeProfileParameter := E × RadianParameter

private def compactProfileWholeIntegrand (a : E → E → E → ℂ) (q : WholeProfileParameter) (y : E) : ℂ :=
  patchFourierPhase (-q.1) y * radianTwoPointParameter a y q.2

private theorem actual_patch_phase_joint_smooth :
    ContDiff ℝ ∞ (fun p : E × E => patchFourierPhase p.1 p.2) := by
  have ih : ContDiff ℝ ∞ (fun p : E × E => inner ℝ p.1 p.2) := contDiff_inner
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul ih)).mul contDiff_const)

private theorem compact_profile_whole_integrand_joint_smooth
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) :
    ContDiff ℝ ∞ (fun q : E × WholeProfileParameter => compactProfileWholeIntegrand a q.2 q.1) := by
  let b (q : E × WholeProfileParameter) : E × E := (-q.2.1,q.1)
  let c (q : E × WholeProfileParameter) : E × RadianParameter := (q.1,q.2.2)
  have bs : ContDiff ℝ ∞ b := (contDiff_fst.comp contDiff_snd).neg.prodMk contDiff_fst
  have cs : ContDiff ℝ ∞ c := contDiff_fst.prodMk (contDiff_snd.comp contDiff_snd)
  change ContDiff ℝ ∞ (fun q => ((fun p : E × E => patchFourierPhase p.1 p.2) ∘ b) q *
    (Function.uncurry (radianTwoPointParameter a) ∘ c) q)
  exact (actual_patch_phase_joint_smooth.comp bs).mul
    ((radian_two_point_parameter_joint_smooth a Rx Ry h).comp cs)

/-- The input Fourier profile of the same physical amplitude is
jointly smooth in its input Fourier frequency and both symbol
variables. Local domination uses the genuine compact input window. -/
theorem compact_radian_parameter_profile_joint_smooth
    (a : E → E → E → ℂ) (Rx Ry : ℝ) (h : CompactRadianTwoPointOrderOne a Rx Ry) :
    ContDiff ℝ ∞ (fun q : E × RadianParameter =>
      compactRadianParameterProfile a Rx Ry h q.1 q.2) := by
  have eq : (fun q : E × RadianParameter => compactRadianParameterProfile a Rx Ry h q.1 q.2) =
      (fun q => ∫ y, compactProfileWholeIntegrand a q y) := by
    funext q
    exact radian_fourier_neg_phase_smul_integral
      ((compactRadianTwoPointSlice a Rx Ry h q.2.1 q.2.2 : SchwartzMap E ℂ) : E → ℂ) q.1
  rw [eq]
  let K := closedBall (0 : E) Ry
  have sub : ∀ y ∉ K, (fun q => compactProfileWholeIntegrand a q y) = 0 := by
    intro y hy
    funext q
    change patchFourierPhase (-q.1) y * a q.2.1 y q.2.2 = 0
    rw [h.inputSupport q.2.1 y q.2.2 hy,mul_zero]
  let μ : Measure E := volume
  have J := dominated_integral_jets_of_uniform_compact_support μ
    (fun y q => compactProfileWholeIntegrand a q y)
    (compact_profile_whole_integrand_joint_smooth a Rx Ry h) K (isCompact_closedBall _ _)
    (isCompact_closedBall (0 : E) Ry).measure_lt_top sub
  exact contDiff_integral_of_dominated_jets μ (compactProfileWholeIntegrand a) J

end Burnett.A03
