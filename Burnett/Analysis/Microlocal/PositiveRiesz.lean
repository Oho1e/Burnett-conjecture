import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.Topology.ContinuousMap.Star

/-!
# Riesz representation of positive continuous functionals

Square positivity on a dense family yields a finite regular measure and
representation on all complex continuous tests. Constant-vector
compressions use the same test space.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.DenseComplexFunctional

open MeasureTheory Set
open scoped CompactlySupported

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Positivity of the complex functional on squares passes from a dense test
family to every continuous square in the uniform norm. -/
theorem preserves_square_positivity_of_dense
    (F : C(X, ℂ) →L[ℂ] ℂ) (D : Set C(X, ℂ)) (hD : Dense D)
    (h : ∀ f ∈ D, 0 ≤ (F (star f * f)).re ∧ (F (star f * f)).im = 0) :
    ∀ f : C(X, ℂ), 0 ≤ (F (star f * f)).re ∧ (F (star f * f)).im = 0 := by
  intro f
  have hf : Continuous (fun g : C(X, ℂ) => F (star g * g)) :=
    F.continuous.comp (continuous_star.mul continuous_id)
  apply hD.denseRange_val.induction_on
    (p := fun g => 0 ≤ (F (star g * g)).re ∧ (F (star g * g)).im = 0) f
  · exact (isClosed_le continuous_const (Complex.continuous_re.comp hf)).inter
      (isClosed_eq (Complex.continuous_im.comp hf) continuous_const)
  · exact fun g => h g g.property

private def realTest (g : C_c(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x => (g x : ℂ), Complex.continuous_ofReal.comp g.continuous⟩

omit [CompactSpace X] in
private theorem realTest_sub (g h : C_c(X, ℝ)) :
    realTest (g - h) = realTest g - realTest h := by
  apply ContinuousMap.ext
  intro x
  exact Complex.ofReal_sub _ _

omit [CompactSpace X] in
private theorem exists_square_of_nonneg_realTest (g : C_c(X, ℝ)) (hg : 0 ≤ g) :
    ∃ z : C(X, ℂ), star z * z = realTest g := by
  let z : C(X, ℂ) :=
    ⟨fun x => (Real.sqrt (g x) : ℂ),
      Complex.continuous_ofReal.comp (Real.continuous_sqrt.comp g.continuous)⟩
  refine ⟨z, ?_⟩
  apply ContinuousMap.ext
  intro x
  change star ((Real.sqrt (g x) : ℝ) : ℂ) * ((Real.sqrt (g x) : ℝ) : ℂ) = (g x : ℂ)
  rw [Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul, Real.mul_self_sqrt (hg x)]

private theorem im_realTest_eq_zero (F : C(X, ℂ) →L[ℂ] ℂ)
    (hF : ∀ g : C(X, ℂ), (F (star g * g)).im = 0) (g : C_c(X, ℝ)) :
    (F (realTest g)).im = 0 := by
  let gp : C_c(X, ℝ) := ⟨⟨fun x => max (g x) 0, g.continuous.max continuous_const⟩,
    HasCompactSupport.of_compactSpace _⟩
  let gm : C_c(X, ℝ) := ⟨⟨fun x => max (-g x) 0, g.continuous.neg.max continuous_const⟩,
    HasCompactSupport.of_compactSpace _⟩
  have hp : 0 ≤ gp := fun x => le_max_right (g x) 0
  have hm : 0 ≤ gm := fun x => le_max_right (-g x) 0
  have heq : g = gp - gm := by
    apply CompactlySupportedContinuousMap.ext
    intro x
    change g x = max (g x) 0 - max (-g x) 0
    rcases le_total 0 (g x) with h | h
    · rw [max_eq_left h, max_eq_right (neg_nonpos.mpr h), sub_zero]
    · rw [max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_sub, neg_neg]
  obtain ⟨zp, hzp⟩ := exists_square_of_nonneg_realTest gp hp
  obtain ⟨zm, hzm⟩ := exists_square_of_nonneg_realTest gm hm
  calc
    (F (realTest g)).im = (F (realTest gp - realTest gm)).im := by rw [← realTest_sub, ← heq]
    _ = 0 := by rw [map_sub, Complex.sub_im, ← hzp, ← hzm, hF, hF, sub_zero]

private def realRestriction (F : C(X, ℂ) →L[ℂ] ℂ) : C_c(X, ℝ) →ₗ[ℝ] ℝ where
  toFun g := (F (realTest g)).re
  map_add' g h := by
    have heq : realTest (g + h) = realTest g + realTest h := by
      apply ContinuousMap.ext
      intro x
      exact Complex.ofReal_add _ _
    change (F (realTest (g + h))).re = (F (realTest g)).re + (F (realTest h)).re
    rw [heq, F.map_add, Complex.add_re]
  map_smul' r g := by
    have heq : realTest (r • g) = (r : ℂ) • realTest g := by
      apply ContinuousMap.ext
      intro x
      exact Complex.ofReal_mul _ _
    change (F (realTest (r • g))).re = r * (F (realTest g)).re
    rw [heq, F.map_smul]
    exact Complex.re_ofReal_mul _ _

/-- A complex functional positive on continuous absolute squares induces a
positive real-linear functional on genuine compactly supported tests. -/
def positiveRealRestriction (F : C(X, ℂ) →L[ℂ] ℂ)
    (hF : ∀ g : C(X, ℂ), 0 ≤ (F (star g * g)).re) : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk₀ (realRestriction F) fun g hg => by
    obtain ⟨z, hz⟩ := exists_square_of_nonneg_realTest g hg
    change 0 ≤ (F (realTest g)).re
    rw [← hz]
    exact hF z

variable [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The actual RMK measure represents every real continuous compactly
supported test with the same positive functional. -/
theorem exists_measure_of_dense_square_positive
    (F : C(X, ℂ) →L[ℂ] ℂ) (D : Set C(X, ℂ)) (hD : Dense D)
    (h : ∀ f ∈ D, 0 ≤ (F (star f * f)).re ∧ (F (star f * f)).im = 0) :
    ∃ μ : Measure X, μ.Regular ∧ ∀ g : C_c(X, ℝ),
      (∫ x, g x ∂μ) = (F (realTest g)).re := by
  let P := positiveRealRestriction F (fun f => (preserves_square_positivity_of_dense F D hD h f).1)
  have hRegular : (RealRMK.rieszMeasure P).Regular := by
    unfold RealRMK.rieszMeasure
    infer_instance
  refine ⟨RealRMK.rieszMeasure P, hRegular, ?_⟩
  intro g
  exact RealRMK.integral_rieszMeasure P g

/-- The scalar Radon measure represents the whole complex functional on the
compact chart test space. One measure is used for every continuous test. -/
theorem exists_measure_representing_dense_square_positive
    (F : C(X, ℂ) →L[ℂ] ℂ) (D : Set C(X, ℂ)) (hD : Dense D)
    (h : ∀ f ∈ D, 0 ≤ (F (star f * f)).re ∧ (F (star f * f)).im = 0) :
    ∃ μ : Measure X, μ.Regular ∧ IsFiniteMeasure μ ∧ ∀ f : C(X, ℂ),
      (∫ x, f x ∂μ) = F f := by
  obtain ⟨μ, hRegular, hR⟩ := exists_measure_of_dense_square_positive F D hD h
  letI : μ.Regular := hRegular
  letI : IsFiniteMeasure μ := ⟨isCompact_univ.measure_lt_top⟩
  have hre (g : C_c(X, ℝ)) : ((∫ x, g x ∂μ : ℝ) : ℂ) = F (realTest g) :=
    Complex.ext (hR g)
      ((im_realTest_eq_zero F (fun f => (preserves_square_positivity_of_dense F D hD h f).2) g).symm)
  have hint (g : C_c(X, ℝ)) : Integrable (realTest g) μ :=
    (realTest g).continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  refine ⟨μ, hRegular, inferInstance, ?_⟩
  intro f
  let a : C_c(X, ℝ) := ⟨⟨fun x => (f x).re, Complex.continuous_re.comp f.continuous⟩,
    HasCompactSupport.of_compactSpace _⟩
  let b : C_c(X, ℝ) := ⟨⟨fun x => (f x).im, Complex.continuous_im.comp f.continuous⟩,
    HasCompactSupport.of_compactSpace _⟩
  have hsplit : f = realTest a + Complex.I • realTest b := by
    apply ContinuousMap.ext
    intro x
    change f x = ((f x).re : ℂ) + Complex.I * ((f x).im : ℂ)
    rw [mul_comm Complex.I, Complex.re_add_im]
  rw [hsplit, F.map_add, map_smul, smul_eq_mul]
  change (∫ x, realTest a x + Complex.I * realTest b x ∂μ) =
    F (realTest a) + Complex.I * F (realTest b)
  rw [integral_add (hint a) ((hint b).const_mul Complex.I), integral_const_mul]
  change (∫ x, (a x : ℂ) ∂μ) + Complex.I * (∫ x, (b x : ℂ) ∂μ) =
    F (realTest a) + Complex.I * F (realTest b)
  rw [integral_complex_ofReal, integral_complex_ofReal, hre, hre]

section Matrix

variable {ι : Type*} [Fintype ι]

/-- Constant-vector quadratic contraction of a family of complex-linear
matrix-entry functionals on the same compact chart test space. -/
def scalarCompression (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (v : ι → ℂ) :
    C(X, ℂ) →L[ℂ] ℂ := ∑ i, ∑ j, (star (v i) * v j) • F i j

omit [CompactSpace X] [T2Space X] [LocallyCompactSpace X] [MeasurableSpace X] [BorelSpace X] in
theorem scalarCompression_apply (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ)
    (v : ι → ℂ) (f : C(X, ℂ)) :
    scalarCompression F v f = ∑ i, ∑ j, star (v i) * v j * F i j f := by
  simp only [scalarCompression, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- Square positivity on the same dense tests for every constant vector
yields genuine scalar Radon measures for all constant-vector contractions.
Each one represents its contraction on every complex continuous test. -/
theorem exists_quadratic_measures_of_dense_square_positive
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (D : Set C(X, ℂ)) (hD : Dense D)
    (h : ∀ (v : ι → ℂ) (f : C(X, ℂ)), f ∈ D →
      0 ≤ (scalarCompression F v (star f * f)).re ∧
        (scalarCompression F v (star f * f)).im = 0) :
    ∃ ν : (ι → ℂ) → Measure X, ∀ v,
      (ν v).Regular ∧ IsFiniteMeasure (ν v) ∧ ∀ f : C(X, ℂ),
        (∫ x, f x ∂ν v) = ∑ i, ∑ j, star (v i) * v j * F i j f := by
  choose ν hν using fun v =>
    exists_measure_representing_dense_square_positive (scalarCompression F v) D hD (h v)
  exact ⟨ν, fun v => ⟨(hν v).1, (hν v).2.1, fun f =>
    ((hν v).2.2 f).trans (scalarCompression_apply F v f)⟩⟩

end Matrix

end Burnett.Microlocal.DenseComplexFunctional
