import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

set_option autoImplicit false

namespace Burnett.Microlocal.Overlap

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X} {f : X → ℂ}

/-- The measure with density given by the nonnegative part of the real component. -/
noncomputable def positiveMeasureOfComplexDensity (μ : Measure X) (f : X → ℂ) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (f x).re)

theorem isFiniteMeasure_positiveMeasureOfComplexDensity (hf : Integrable f μ) :
    IsFiniteMeasure (positiveMeasureOfComplexDensity μ f) :=
  isFiniteMeasure_withDensity_ofReal (Complex.reCLM.integrable_comp hf).hasFiniteIntegral

/-- The complex Bochner integrals of an almost everywhere nonnegative real
density are the values of the associated positive measure. -/
theorem positiveMeasureOfComplexDensity_apply_eq_setIntegral (hf : Integrable f μ)
    (h : ∀ᵐ x ∂μ, 0 ≤ (f x).re ∧ (f x).im = 0) {s : Set X} (hs : MeasurableSet s) :
    (((positiveMeasureOfComplexDensity μ f) s).toReal : ℂ) = ∫ x in s, f x ∂μ := by
  have hRe : Integrable (fun x => (f x).re) (μ.restrict s) :=
    Complex.reCLM.integrable_comp hf.integrableOn
  have hNonneg : 0 ≤ᵐ[μ.restrict s] (fun x => (f x).re) :=
    ae_restrict_of_ae (h.mono fun _ hx => hx.1)
  rw [positiveMeasureOfComplexDensity, withDensity_apply _ hs,
    ← integral_eq_lintegral_of_nonneg_ae hNonneg hRe.aestronglyMeasurable, ← integral_complex_ofReal]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae h] with x hx
  apply Complex.ext <;> simp only [Complex.ofReal_re, Complex.ofReal_im, hx.2]

/-- The set integrals determine the positive measure among finite measures. -/
theorem eq_positiveMeasureOfComplexDensity_of_setIntegral (hf : Integrable f μ)
    (h : ∀ᵐ x ∂μ, 0 ≤ (f x).re ∧ (f x).im = 0) (ν : Measure X) [IsFiniteMeasure ν]
    (hν : ∀ s, MeasurableSet s → ((ν s).toReal : ℂ) = ∫ x in s, f x ∂μ) :
    ν = positiveMeasureOfComplexDensity μ f := by
  letI := isFiniteMeasure_positiveMeasureOfComplexDensity hf
  apply Measure.ext
  intro s hs
  have hValues : (ν s).toReal = ((positiveMeasureOfComplexDensity μ f) s).toReal :=
    Complex.ofReal_injective
      ((hν s hs).trans (positiveMeasureOfComplexDensity_apply_eq_setIntegral hf h hs).symm)
  calc
    ν s = ENNReal.ofReal (ν s).toReal := (ENNReal.ofReal_toReal (measure_ne_top ν s)).symm
    _ = ENNReal.ofReal ((positiveMeasureOfComplexDensity μ f) s).toReal := congrArg ENNReal.ofReal hValues
    _ = _ := ENNReal.ofReal_toReal (measure_ne_top _ s)

end Burnett.Microlocal.Overlap
