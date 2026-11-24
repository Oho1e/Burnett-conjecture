import Burnett.Analysis.Microlocal.Overlap.PositiveMeasureOfComplexDensity

/-! Restrictions, measurable subtype pullbacks and weights of finite positive densities. -/

set_option autoImplicit false

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open scoped ENNReal

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

theorem restrict_positiveMeasureOfComplexDensity
    (μ : Measure X) (f : X → ℂ) {s : Set X} (hs : MeasurableSet s) :
    (positiveMeasureOfComplexDensity μ f).restrict s =
      positiveMeasureOfComplexDensity (μ.restrict s) f :=
  restrict_withDensity hs _

theorem comap_positiveMeasureOfComplexDensity_subtype
    (μ : Measure X) (f : X → ℂ) {s : Set X} (hs : MeasurableSet s) :
    (positiveMeasureOfComplexDensity μ f).comap (Subtype.val : s → X) =
      positiveMeasureOfComplexDensity (μ.comap Subtype.val) (fun x : s => f x.1) := by
  apply Measure.ext
  intro t ht
  have ht' : MeasurableSet ((Subtype.val : s → X) '' t) :=
    (MeasurableEmbedding.subtype_coe hs).measurableSet_image.mpr ht
  unfold positiveMeasureOfComplexDensity
  rw [comap_subtype_coe_apply hs, withDensity_apply _ ht', withDensity_apply _ ht]
  exact (setLIntegral_subtype (μ := μ) hs t (fun x : X => ENNReal.ofReal (f x).re)).symm

/-- Multiplication by a nonnegative measurable weight commutes with taking the
positive part of the real component of a complex density. -/
theorem positiveMeasureOfComplexDensity_withDensity_ofReal
    (μ : Measure X) (f : X → ℂ) (hf : AEMeasurable f μ)
    (w : X → ℝ) (hw : Measurable w) (hn : ∀ x, 0 ≤ w x) :
    (positiveMeasureOfComplexDensity μ f).withDensity (fun x => ENNReal.ofReal (w x)) =
      positiveMeasureOfComplexDensity μ (fun x => (w x : ℂ) * f x) := by
  have hf' : AEMeasurable (fun x => ENNReal.ofReal (f x).re) μ :=
    (Complex.continuous_re.measurable.comp_aemeasurable hf).ennreal_ofReal
  unfold positiveMeasureOfComplexDensity
  rw [← withDensity_mul₀ hf' hw.ennreal_ofReal.aemeasurable]
  congr 1
  funext x
  simp only [Pi.mul_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [ENNReal.ofReal_mul (hn x), mul_comm]

/-- Equality of all complex Borel set integrals transports the associated finite
measures when both restricted densities are almost everywhere real and nonnegative. -/
theorem map_positiveMeasureOfComplexDensity_eq_of_setIntegral
    (μ : Measure X) (ν : Measure Y) (f : X → ℂ) (g : Y → ℂ)
    (T : X → Y) (hT : Measurable T) (U : Set X) (V : Set Y)
    (hf : Integrable f (μ.restrict U)) (hg : Integrable g (ν.restrict V))
    (hfp : ∀ᵐ x ∂μ.restrict U, 0 ≤ (f x).re ∧ (f x).im = 0)
    (hgp : ∀ᵐ y ∂ν.restrict V, 0 ≤ (g y).re ∧ (g y).im = 0)
    (hCov : ∀ S : Set Y, MeasurableSet S →
      (∫ x in (T ⁻¹' S) ∩ U, f x ∂μ) = ∫ y in S ∩ V, g y ∂ν) :
    (positiveMeasureOfComplexDensity (μ.restrict U) f).map T =
      positiveMeasureOfComplexDensity (ν.restrict V) g := by
  letI : IsFiniteMeasure (positiveMeasureOfComplexDensity (μ.restrict U) f) :=
    isFiniteMeasure_positiveMeasureOfComplexDensity hf
  letI : IsFiniteMeasure ((positiveMeasureOfComplexDensity (μ.restrict U) f).map T) :=
    Measure.isFiniteMeasure_map _ T
  apply eq_positiveMeasureOfComplexDensity_of_setIntegral hg hgp
  intro S hS
  rw [Measure.map_apply hT hS,
    positiveMeasureOfComplexDensity_apply_eq_setIntegral hf hfp (hT hS),
    Measure.restrict_restrict (hT hS), Measure.restrict_restrict hS]
  exact hCov S hS

end Burnett.Microlocal.Overlap
