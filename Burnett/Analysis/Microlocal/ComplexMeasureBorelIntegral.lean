import Burnett.Analysis.Microlocal.WeightedBorelRestriction
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.RadonNikodym

set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section

namespace Burnett.Microlocal

open Set MeasureTheory LocalMeasureComparison
open scoped BigOperators

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

def complexMeasureTestReference (m : ComplexMeasure X) : Measure X :=
  m.re.totalVariation + m.im.totalVariation

private theorem complexMeasureTestReference_finite (m : ComplexMeasure X) :
    IsFiniteMeasure (complexMeasureTestReference m) := by
  unfold complexMeasureTestReference SignedMeasure.totalVariation
  infer_instance

private theorem complexMeasureTestReference_dominates (m : ComplexMeasure X) :
    m ≪ᵥ (complexMeasureTestReference m).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro A hA hz
  rw [Measure.toENNRealVectorMeasure_apply_measurable hA,
    complexMeasureTestReference, Measure.add_apply] at hz
  have hz' := add_eq_zero.mp hz
  apply Complex.ext
  · change m.re A = 0
    exact SignedMeasure.null_of_totalVariation_zero _ hz'.1
  · change m.im A = 0
    exact SignedMeasure.null_of_totalVariation_zero _ hz'.2

theorem complexMeasure_reference_setIntegral (m : ComplexMeasure X) (A : Set X) (hA : MeasurableSet A) :
    (∫ x in A, m.rnDeriv (complexMeasureTestReference m) x ∂complexMeasureTestReference m) = m A := by
  let μ := complexMeasureTestReference m
  letI : IsFiniteMeasure μ := complexMeasureTestReference_finite m
  have hAC := (ComplexMeasure.absolutelyContinuous_ennreal_iff m μ.toENNRealVectorMeasure).mp
    (complexMeasureTestReference_dominates m)
  have hI := (ComplexMeasure.integrable_rnDeriv m μ).integrableOn (s := A)
  change (∫ x in A, m.rnDeriv μ x ∂μ) = m A
  apply Complex.ext
  · change RCLike.re (∫ x in A, m.rnDeriv μ x ∂μ) = _
    rw [← integral_re hI]
    change (∫ x in A, m.re.rnDeriv μ x ∂μ) = m.re A
    rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv m.re μ) hA,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hAC.1]
  · change RCLike.im (∫ x in A, m.rnDeriv μ x ∂μ) = _
    rw [← integral_im hI]
    change (∫ x in A, m.im.rnDeriv μ x ∂μ) = m.im A
    rw [← withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv m.im μ) hA,
      SignedMeasure.withDensityᵥ_rnDeriv_eq _ _ hAC.2]

/-- The integral of a bounded Borel test against a finite complex measure,
using the total variations of its real and imaginary parts. -/
def complexMeasureBorelIntegral (m : ComplexMeasure X) (f : X → ℂ) : ℂ :=
  ∫ x, f x * m.rnDeriv (complexMeasureTestReference m) x ∂complexMeasureTestReference m

theorem complexMeasureBorelIntegral_eq_of_setIntegrals (m : ComplexMeasure X)
    (ν : Measure Y) (F : Y → X) (hF : Measurable F) (a : Y → ℂ) (ha : Integrable a ν)
    (h : ∀ A : Set X, MeasurableSet A → m A = ∫ y in F ⁻¹' A, a y ∂ν)
    (f : X → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    complexMeasureBorelIntegral m f = ∫ y, f (F y) * a y ∂ν := by
  unfold complexMeasureBorelIntegral
  exact integral_weight_eq_of_setIntegrals (complexMeasureTestReference m) ν id F measurable_id hF
    (m.rnDeriv (complexMeasureTestReference m)) a (m.integrable_rnDeriv _) ha
    (fun A hA => (complexMeasure_reference_setIntegral m A hA).trans (h A hA)) f hf C hC hbound

theorem complexMeasureBorelIntegral_map_withDensity (ν : Measure Y) (F : Y → X)
    (hF : Measurable F) (a : Y → ℂ) (ha : Integrable a ν)
    (f : X → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    complexMeasureBorelIntegral ((ν.withDensityᵥ a).map F) f = ∫ y, f (F y) * a y ∂ν := by
  refine complexMeasureBorelIntegral_eq_of_setIntegrals _ ν F hF a ha ?_ f hf C hC hbound
  intro A hA
  rw [VectorMeasure.map_apply _ hF hA, withDensityᵥ_apply ha (hF hA)]

theorem complexMeasureBorelIntegral_restrict (m : ComplexMeasure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C) :
    complexMeasureBorelIntegral (m.restrict S) f =
      ∫ x in S, f x * m.rnDeriv (complexMeasureTestReference m) x ∂complexMeasureTestReference m := by
  refine complexMeasureBorelIntegral_eq_of_setIntegrals _ _ id measurable_id _
    (m.integrable_rnDeriv _).integrableOn ?_ f hf C hC hbound
  intro A hA
  change m.restrict S A = ∫ x in A, m.rnDeriv (complexMeasureTestReference m) x ∂(complexMeasureTestReference m).restrict S
  rw [VectorMeasure.restrict_apply _ hS hA, Measure.restrict_restrict hA]
  exact (complexMeasure_reference_setIntegral m (A ∩ S) (hA.inter hS)).symm

/-- A weight supported on a measurable region only uses the restriction of
the complex measure to that region. -/
theorem complexMeasureBorelIntegral_eq_of_support (m : ComplexMeasure X) (S : Set X) (hS : MeasurableSet S)
    (f : X → ℂ) (hf : Measurable f) (C : ℝ) (hC : 0 ≤ C) (hbound : ∀ x, ‖f x‖ ≤ C)
    (hzero : ∀ x ∉ S, f x = 0) :
    complexMeasureBorelIntegral m f = complexMeasureBorelIntegral (m.restrict S) f := by
  rw [complexMeasureBorelIntegral_restrict m S hS f hf C hC hbound,
    complexMeasureBorelIntegral, ← integral_indicator hS]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ S <;> simp [hx, hzero x]

theorem complexMeasureBorelIntegral_sum {ι : Type*} (T : Finset ι) (m : ComplexMeasure X) (f : ι → X → ℂ)
    (hf : ∀ i ∈ T, Measurable (f i)) (C : ι → ℝ)
    (hbound : ∀ i ∈ T, ∀ x, ‖f i x‖ ≤ C i) :
    complexMeasureBorelIntegral m (fun x => ∑ i ∈ T, f i x) =
      ∑ i ∈ T, complexMeasureBorelIntegral m (f i) := by
  simp only [complexMeasureBorelIntegral, Finset.sum_mul]
  exact integral_finset_sum _ fun i hi => (m.integrable_rnDeriv _).bdd_mul'
    (hf i hi).aestronglyMeasurable (Filter.Eventually.of_forall (hbound i hi))

end Burnett.Microlocal
