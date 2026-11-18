import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Continuous tests determine finite combinations of measures

The positive and negative finite sums are compared by their continuous
test integrals. The complex case applies this to both real components.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.MeasureSeparation

open MeasureTheory Set
open scoped NNReal ENNReal

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [BorelSpace X] [HasOuterApproxClosed X]
variable {ι : Type*} [Fintype ι]

private def weighted (μ : ι → Measure X) (r : ι → ℝ≥0) : Measure X :=
  ∑ i, r i • μ i

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
private theorem weighted_isFinite (μ : ι → Measure X) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (r : ι → ℝ≥0) : IsFiniteMeasure (weighted μ r) := by
  classical
  unfold weighted
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    infer_instance
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    letI : IsFiniteMeasure (μ i) := hμ i
    letI : IsFiniteMeasure (∑ j ∈ s, r j • μ j) := ih
    infer_instance

omit [HasOuterApproxClosed X] in
private theorem integral_weighted (μ : ι → Measure X) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (r : ι → ℝ≥0) (f : C(X, ℝ)) :
    (∫ x, f x ∂(weighted μ r)) = ∑ i, (r i : ℝ) * ∫ x, f x ∂μ i := by
  unfold weighted
  rw [integral_finset_sum_measure]
  · simp only [integral_smul_nnreal_measure, NNReal.smul_def, smul_eq_mul]
  · intro i _
    letI : IsFiniteMeasure (μ i) := hμ i
    exact f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

omit [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X] in
private theorem weighted_real (μ : ι → Measure X) (hμ : ∀ i, IsFiniteMeasure (μ i))
    (r : ι → ℝ≥0) (s : Set X) :
    (weighted μ r).real s = ∑ i, (r i : ℝ) * (μ i).real s := by
  unfold weighted
  rw [measureReal_def, Measure.finset_sum_apply, ENNReal.toReal_sum]
  · simp only [measureReal_def, Measure.coe_nnreal_smul_apply, ENNReal.toReal_mul,
      ENNReal.coe_toReal]
  · intro i _
    letI : IsFiniteMeasure (μ i) := hμ i
    rw [Measure.coe_nnreal_smul_apply]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)

private theorem real_eq_toNNReal_sub (t : ℝ) :
    t = (t.toNNReal : ℝ) - ((-t).toNNReal : ℝ) := by
  change t = max t 0 - max (-t) 0
  rcases le_total 0 t with h | h
  · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
  · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]

/-- A finite real combination of finite measures which annihilates all
continuous tests vanishes on every Borel set. The proof compares the actual
positive and negative weighted sums of finite measures. -/
theorem sum_measure_real_eq_zero_of_integral_eq_zero (μ : ι → Measure X)
    (hμ : ∀ i, IsFiniteMeasure (μ i)) (r : ι → ℝ)
    (h : ∀ f : C(X, ℝ), ∑ i, r i * (∫ x, f x ∂μ i) = 0) :
    ∀ s : Set X, ∑ i, r i * (μ i).real s = 0 := by
  let p (i : ι) := (r i).toNNReal
  let n (i : ι) := (-r i).toNNReal
  have hp (i : ι) : r i = (p i : ℝ) - (n i : ℝ) := real_eq_toNNReal_sub (r i)
  letI : IsFiniteMeasure (weighted μ p) := weighted_isFinite μ hμ p
  letI : IsFiniteMeasure (weighted μ n) := weighted_isFinite μ hμ n
  have heq : weighted μ p = weighted μ n := by
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    change (∫ x, f.toContinuousMap x ∂weighted μ p) = ∫ x, f.toContinuousMap x ∂weighted μ n
    rw [integral_weighted μ hμ, integral_weighted μ hμ]
    apply sub_eq_zero.mp
    have hh := h f.toContinuousMap
    simp_rw [hp, sub_mul, Finset.sum_sub_distrib] at hh
    exact hh
  intro s
  have hs := congrArg (fun ν : Measure X => ν.real s) heq
  change (weighted μ p).real s = (weighted μ n).real s at hs
  rw [weighted_real μ hμ, weighted_real μ hμ] at hs
  simp_rw [hp, sub_mul, Finset.sum_sub_distrib]
  exact sub_eq_zero.mpr hs

/-- Continuous real tests also separate finite complex combinations of
finite positive measures, by applying the real result to both components. -/
theorem sum_complex_measure_real_eq_zero_of_integral_eq_zero (μ : ι → Measure X)
    (hμ : ∀ i, IsFiniteMeasure (μ i)) (c : ι → ℂ)
    (h : ∀ f : C(X, ℝ),
      ∑ i, c i * ((∫ x, f x ∂μ i : ℝ) : ℂ) = 0) :
    ∀ s : Set X, ∑ i, c i * ((μ i).real s : ℂ) = 0 := by
  have hRe (f : C(X, ℝ)) : ∑ i, (c i).re * (∫ x, f x ∂μ i) = 0 := by
    simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.zero_re] using congrArg Complex.re (h f)
  have hIm (f : C(X, ℝ)) : ∑ i, (c i).im * (∫ x, f x ∂μ i) = 0 := by
    simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, Complex.zero_im] using congrArg Complex.im (h f)
  intro s
  apply Complex.ext
  · simpa only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, sub_zero, Complex.zero_re] using
      sum_measure_real_eq_zero_of_integral_eq_zero μ hμ (fun i => (c i).re) hRe s
  · simpa only [Complex.im_sum, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      mul_zero, zero_add, Complex.zero_im] using
      sum_measure_real_eq_zero_of_integral_eq_zero μ hμ (fun i => (c i).im) hIm s

end Burnett.Microlocal.MeasureSeparation
