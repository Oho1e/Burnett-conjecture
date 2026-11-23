import Mathlib.MeasureTheory.Function.SimpleFuncDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 3400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set
open scoped Topology

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

private theorem integrable_simple_mul
    (μ : Measure X) (φ : X → Y) (hφ : Measurable φ)
    (f : X → ℂ) (hf : Integrable f μ) (a : SimpleFunc Y ℂ) :
    Integrable (fun x => a (φ x) * f x) μ := by
  obtain ⟨B, hB⟩ := a.finite_range.isBounded.exists_norm_le
  exact hf.bdd_mul (a.measurable.comp hφ).aestronglyMeasurable ⟨B, fun x => hB _ ⟨φ x, rfl⟩⟩

private theorem integral_mul_simple_eq_of_setIntegral_preimage_eq
    (μ : Measure X) (ν : Measure Y) (φ : X → Y) (hφ : Measurable φ)
    (f : X → ℂ) (g : Y → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ S : Set Y, MeasurableSet S → (∫ x in φ ⁻¹' S, f x ∂μ) = ∫ y in S, g y ∂ν)
    (a : SimpleFunc Y ℂ) :
    (∫ x, a (φ x) * f x ∂μ) = ∫ y, a y * g y ∂ν := by
  induction a using SimpleFunc.induction with
  | @const c S hS =>
      let p := SimpleFunc.piecewise S hS (SimpleFunc.const Y c) (SimpleFunc.const Y 0)
      change (∫ x, p (φ x) * f x ∂μ) = ∫ y, p y * g y ∂ν
      have hL : (fun x => p (φ x) * f x) = (φ ⁻¹' S).indicator (fun x => c * f x) := by
        funext x
        by_cases hx : φ x ∈ S
        · have hpx : x ∈ φ ⁻¹' S := hx
          simp only [p, SimpleFunc.piecewise_apply, hx, if_true, SimpleFunc.const_apply, indicator_of_mem hpx]
        · have hpx : x ∉ φ ⁻¹' S := hx
          simp only [p, SimpleFunc.piecewise_apply, hx, if_false, SimpleFunc.const_apply,
            zero_mul, indicator_of_notMem hpx]
      have hR : (fun y => p y * g y) = S.indicator (fun y => c * g y) := by
        funext y
        by_cases hy : y ∈ S
        · simp only [p, SimpleFunc.piecewise_apply, hy, if_true, SimpleFunc.const_apply, indicator_of_mem hy]
        · simp only [p, SimpleFunc.piecewise_apply, hy, if_false, SimpleFunc.const_apply,
            zero_mul, indicator_of_notMem hy]
      rw [hL, hR, integral_indicator (hφ hS), integral_indicator hS,
        integral_const_mul, integral_const_mul, h S hS]
  | @add p q _ hp hq =>
      have hL := integral_add (integrable_simple_mul μ φ hφ f hf p) (integrable_simple_mul μ φ hφ f hf q)
      have hR := integral_add (integrable_simple_mul ν id measurable_id g hg p)
        (integrable_simple_mul ν id measurable_id g hg q)
      simpa only [SimpleFunc.add_apply, add_mul] using
        (hL.trans (congrArg₂ (· + ·) hp hq)).trans hR.symm

/-- A Borel-set entry identity passes to every bounded measurable
multiplicative test on the same target. -/
theorem integral_mul_eq_of_setIntegral_preimage_eq
    (μ : Measure X) (ν : Measure Y) (φ : X → Y) (hφ : Measurable φ)
    (f : X → ℂ) (g : Y → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ S : Set Y, MeasurableSet S → (∫ x in φ ⁻¹' S, f x ∂μ) = ∫ y in S, g y ∂ν)
    (a : Y → ℂ) (ha : Measurable a) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ y, ‖a y‖ ≤ B) :
    (∫ x, a (φ x) * f x ∂μ) = ∫ y, a y * g y ∂ν := by
  let K := Metric.closedBall (0 : ℂ) B
  have h0 : 0 ∈ K := Metric.mem_closedBall_self hB
  let Q (n : ℕ) := SimpleFunc.approxOn a ha K 0 h0 n
  have hQ (n : ℕ) (y : Y) : ‖Q n y‖ ≤ B := by
    have hy : Q n y ∈ K := SimpleFunc.approxOn_mem ha h0 n y
    simpa only [K, Metric.mem_closedBall, dist_zero_right] using hy
  have hP (y : Y) : Tendsto (fun n => Q n y) atTop (𝓝 (a y)) :=
    SimpleFunc.tendsto_approxOn ha h0 (subset_closure (by
      simpa only [K, Metric.mem_closedBall, dist_zero_right] using hA y))
  have hX := tendsto_integral_of_dominated_convergence (μ := μ) (fun x => B * ‖f x‖)
    (fun n => ((Q n).measurable.comp hφ).aestronglyMeasurable.mul hf.aestronglyMeasurable)
    (hf.norm.const_mul B)
    (fun n => Eventually.of_forall fun x => (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right (hQ n (φ x)) (norm_nonneg _)))
    (Eventually.of_forall fun x => (hP (φ x)).mul_const (f x))
  have hY := tendsto_integral_of_dominated_convergence (μ := ν) (fun y => B * ‖g y‖)
    (fun n => (Q n).measurable.aestronglyMeasurable.mul hg.aestronglyMeasurable)
    (hg.norm.const_mul B)
    (fun n => Eventually.of_forall fun y => (norm_mul _ _).le.trans
      (mul_le_mul_of_nonneg_right (hQ n y) (norm_nonneg _)))
    (Eventually.of_forall fun y => (hP y).mul_const (g y))
  have he : (fun n => ∫ x, Q n (φ x) * f x ∂μ) =
      fun n => ∫ y, Q n y * g y ∂ν :=
    funext fun n => integral_mul_simple_eq_of_setIntegral_preimage_eq μ ν φ hφ f g hf hg h (Q n)
  change Tendsto (fun n => ∫ x, Q n (φ x) * f x ∂μ) atTop _ at hX
  rw [he] at hX
  exact tendsto_nhds_unique hX hY

/-- The same bounded measurable weight can be inserted on any target
Borel set and its corresponding source preimage. -/
theorem setIntegral_mul_eq_of_setIntegral_preimage_eq
    (μ : Measure X) (ν : Measure Y) (φ : X → Y) (hφ : Measurable φ)
    (f : X → ℂ) (g : Y → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ S : Set Y, MeasurableSet S → (∫ x in φ ⁻¹' S, f x ∂μ) = ∫ y in S, g y ∂ν)
    (a : Y → ℂ) (ha : Measurable a) (B : ℝ) (hB : 0 ≤ B) (hA : ∀ y, ‖a y‖ ≤ B)
    (S : Set Y) (hS : MeasurableSet S) :
    (∫ x in φ ⁻¹' S, a (φ x) * f x ∂μ) = ∫ y in S, a y * g y ∂ν := by
  have hBound (y : Y) : ‖S.indicator a y‖ ≤ B := by
    by_cases hy : y ∈ S
    · simpa only [indicator_of_mem hy] using hA y
    · simpa only [indicator_of_notMem hy, norm_zero] using hB
  have hEq := integral_mul_eq_of_setIntegral_preimage_eq μ ν φ hφ f g hf hg h
    (S.indicator a) (ha.indicator hS) B hB hBound
  have hL : (fun x => S.indicator a (φ x) * f x) =
      (φ ⁻¹' S).indicator (fun x => a (φ x) * f x) := by
    funext x
    by_cases hx : φ x ∈ S
    · have hpx : x ∈ φ ⁻¹' S := hx
      rw [indicator_of_mem hx, indicator_of_mem hpx]
    · have hpx : x ∉ φ ⁻¹' S := hx
      rw [indicator_of_notMem hx, indicator_of_notMem hpx, zero_mul]
  have hR : (fun y => S.indicator a y * g y) = S.indicator (fun y => a y * g y) := by
    funext y
    by_cases hy : y ∈ S
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, zero_mul]
  rw [hL, hR, integral_indicator (hφ hS), integral_indicator hS] at hEq
  exact hEq

end Burnett.Microlocal.Overlap
