import Burnett.Analysis.SignedFourierWindow.PhysicalDifferences
import Burnett.Analysis.SignedFourierWindow.CalderonCancellation

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section
namespace Burnett.A06

open MeasureTheory Metric Set
open Burnett.Analysis.SignedFourierWindow
open Filter
open scoped Topology

abbrev CoefficientSpace := EuclideanSpace ℝ (Fin 4)

/-- Contributions outside the doubled receiving ball to the actual normalized
Schwartz convolution carry a factor of its physical scale over the radius. -/
theorem coefficientWindow_off_doubled_ball
    (ψ : SchwartzMap CoefficientSpace ℂ) {s R : ℝ} (hs : 0<s) (hR : 0<R)
    (center x : CoefficientSpace) (hx : x ∈ ball center R)
    (F : CoefficientSpace → ℂ) {L : ℝ} (hL : 0≤L) (hF : ∀ y, ‖F y‖ ≤ L) :
    ‖kernelApply (shiftedSpatialKernel ψ s 0) ((ball center (2*R))ᶜ.indicator F) x‖ ≤
      L*(s/R)*(∫ z : CoefficientSpace, ‖z‖*‖ψ z‖) := by
  let K := shiftedSpatialKernel ψ s (0 : CoefficientSpace)
  let S := {z : CoefficientSpace | R≤‖z‖}
  let B := (ball center (2*R))ᶜ
  let major := S.indicator (fun z => L*‖K z‖)
  have hS : MeasurableSet S := (isClosed_le continuous_const continuous_norm).measurableSet
  have hi : Integrable major :=
    ((shiftedSpatialKernel_integrable ψ hs 0).norm.const_mul L).indicator hS
  have ht := (volume : Measure CoefficientSpace).measurePreserving_sub_left x
  have hM := (ht.integrable_comp_emb (Homeomorph.subLeft x).measurableEmbedding).2 hi
  have hsep (y : CoefficientSpace) (hy : y ∈ B) : x-y ∈ S := by
    have hn : 2*R ≤ dist y center := le_of_not_gt (fun h => hy (mem_ball.mpr h))
    have hd := dist_triangle y x center
    rw [dist_comm y x,dist_eq_norm x y] at hd
    exact (show R ≤ ‖x-y‖ by linarith only [hn,hd,mem_ball.mp hx])
  have hdom (y : CoefficientSpace) : ‖K (x-y) * B.indicator F y‖ ≤ major (x-y) := by
    by_cases hy : y ∈ B
    · rw [indicator_of_mem hy,norm_mul,show major (x-y) = L*‖K (x-y)‖ from indicator_of_mem (hsep y hy) _,
        mul_comm L]
      exact mul_le_mul_of_nonneg_left (hF y) (norm_nonneg _)
    · rw [indicator_of_notMem hy,mul_zero,norm_zero]
      exact indicator_nonneg (fun _ _ => mul_nonneg hL (norm_nonneg _)) _
  change ‖∫ y : CoefficientSpace, K (x-y) * B.indicator F y‖ ≤ _
  calc
    _ ≤ ∫ y : CoefficientSpace, ‖K (x-y) * B.indicator F y‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ y : CoefficientSpace, major (x-y) :=
      integral_mono_of_nonneg (.of_forall fun _ => norm_nonneg _) hM (.of_forall hdom)
    _ = ∫ z : CoefficientSpace, major z :=
      ht.integral_comp (Homeomorph.subLeft x).measurableEmbedding major
    _ = L*(∫ z in S, ‖K z‖) := by
      unfold major
      rw [integral_indicator hS,integral_const_mul]
    _ ≤ _ := by
      have htail := shifted_spatial_tail ψ s hs 0 R hR
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (by simpa only [S,K,norm_zero,zero_mul,add_zero] using htail) hL

end Burnett.A06
