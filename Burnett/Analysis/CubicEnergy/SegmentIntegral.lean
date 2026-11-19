import Burnett.Analysis.CubicEnergy.FrequencySplit
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
noncomputable section
namespace Burnett.A02.FrequencySplit
open MeasureTheory Set Filter Metric
open scoped ContDiff Topology Interval

private abbrev P := E × E
private abbrev I := Icc (0:ℝ) 1
private abbrev J := Ioo (-2:ℝ) 2
private theorem subset_time : I ⊆ J := fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
private def firstDerivative (F : P × ℝ → V) (z : P × ℝ) :=
  (fderiv ℝ F z).comp (ContinuousLinearMap.inl ℝ P ℝ)

omit [CompleteSpace V] in
private theorem smooth_first {U : Set P} (hU : IsOpen U) (F : P × ℝ → V)
    (hf : ContDiffOn ℝ ∞ F (U ×ˢ J)) : ContDiffOn ℝ ∞ (firstDerivative F) (U ×ˢ J) :=
  (hf.fderiv_of_isOpen (hU.prod isOpen_Ioo) (by simp)).clm_comp contDiffOn_const

private theorem time_continuous {W : Type} [TopologicalSpace W] {U : Set P} {F : P × ℝ → W}
    (hf : ContinuousOn F (U ×ˢ J)) {p : P} (hp : p ∈ U) :
    ContinuousOn (fun t => F (p,t)) I :=
  hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hp,subset_time ht⟩)

omit [CompleteSpace V] in
private theorem smooth_integral_deriv {U : Set P} (hU : IsOpen U) (F : P × ℝ → V)
    (hf : ContDiffOn ℝ ∞ F (U ×ˢ J)) {p : P} (hp : p ∈ U) :
    HasFDerivAt (fun q => ∫ t in I, F (q,t)) (∫ t in I, firstDerivative F (p,t)) p := by
  obtain ⟨ε,hε,hball⟩ := nhds_basis_closedBall.mem_iff.mp (hU.mem_nhds hp)
  have hd := smooth_first hU F hf
  have hc : IsCompact (closedBall p ε ×ˢ I) := (isCompact_closedBall p ε).prod isCompact_Icc
  obtain ⟨C,hC⟩ := hc.bddAbove_image (hd.continuousOn.norm.mono (Set.prod_mono hball subset_time))
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (μ := volume.restrict I)
    (F := fun x t => F (x,t)) (F' := fun x t => firstDerivative F (x,t)) (bound := fun _ : ℝ => C) hε
  · filter_upwards [hU.mem_nhds hp] with q hq
    exact (time_continuous hf.continuousOn hq).integrableOn_Icc.aestronglyMeasurable
  · exact (time_continuous hf.continuousOn hp).integrableOn_Icc
  · exact (time_continuous hd.continuousOn hp).integrableOn_Icc.aestronglyMeasurable
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
    intro x hx
    exact hC (mem_image_of_mem _ (show (x,t) ∈ closedBall p ε ×ˢ I from ⟨ball_subset_closedBall hx,ht⟩))
  · exact integrableOn_const (measure_Icc_lt_top.ne)
  · filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Icc] with t ht
    intro x hx
    have hxt : (x,t) ∈ U ×ˢ J := ⟨hball (ball_subset_closedBall hx),subset_time ht⟩
    have hxD := ((hf.differentiableOn (by simp)) (x,t) hxt).differentiableAt ((hU.prod isOpen_Ioo).mem_nhds hxt)
    exact hxD.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)

private theorem smooth_integral_nat (n : ℕ) {U : Set P} (hU : IsOpen U) (F : P × ℝ → V)
    (hf : ContDiffOn ℝ ∞ F (U ×ˢ J)) : ContDiffOn ℝ n (fun q => ∫ t in I, F (q,t)) U := by
  induction n generalizing V with
  | zero =>
    apply contDiffOn_zero.mpr
    exact fun p hp => (smooth_integral_deriv hU F hf hp).continuousAt.continuousWithinAt
  | succ n ih =>
    rw [Nat.cast_succ]
    apply (contDiffOn_succ_iff_fderiv_of_isOpen hU).mpr
    refine ⟨fun p hp => (smooth_integral_deriv hU F hf hp).differentiableAt.differentiableWithinAt,by simp,?_⟩
    apply (ih (firstDerivative F) (smooth_first hU F hf)).congr
    intro p hp
    exact (smooth_integral_deriv hU F hf hp).fderiv

theorem smooth_segment_average {U : Set (E × E)} (hU : IsOpen U) (F : (E × E) × ℝ → V)
    (hf : ContDiffOn ℝ ∞ F (U ×ˢ Ioo (-2:ℝ) 2)) :
    ContDiffOn ℝ ∞ (fun q => ∫ t in (0:ℝ)..1, F (q,t)) U := by
  apply (contDiffOn_infty.mpr (fun n => smooth_integral_nat n hU F hf)).congr
  intro p _
  rw [intervalIntegral.integral_of_le zero_le_one,integral_Icc_eq_integral_Ioc]

end Burnett.A02.FrequencySplit
