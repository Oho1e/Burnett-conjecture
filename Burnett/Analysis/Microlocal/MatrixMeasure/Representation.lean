import Burnett.Analysis.Microlocal.PositiveRiesz
import Burnett.Analysis.Microlocal.MatrixMeasure.Assembly
import Mathlib.Data.Complex.BigOperators

/-!
# Representation of positive matrix functionals on a compact space

One family of scalar compression measures represents all continuous
tests. Its polarized complex entries are positive semidefinite on
measurable sets and are dominated by the same finite trace measure.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.MatrixMeasureAssembly

open MeasureTheory Set Burnett.Microlocal.MatrixPolarization
open Burnett.Microlocal.DenseComplexFunctional
open scoped BigOperators ComplexOrder

variable {ι X : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace X]

theorem traceMeasure_isFinite_of_finite_compressions
    (ν : (ι → ℂ) → Measure X) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    IsFiniteMeasure (traceMeasure ν) := by
  refine ⟨?_⟩
  rw [traceMeasure, Measure.finset_sum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  letI := hfin (Pi.single i 1)
  exact measure_lt_top _ _

variable [TopologicalSpace X] [CompactSpace X] [BorelSpace X] [HasOuterApproxClosed X]

theorem entryMeasure_trace_apply
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v)
    (s : Set X) (hs : MeasurableSet s) :
    Matrix.trace (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ) =
      ((traceMeasure ν).real s : ℂ) := by
  have hDiag (i : ι) :
      entryMeasure ν hfin i i s = ((ν (Pi.single i 1)).real s : ℂ) := by
    have h := quadratic_entryMeasure_apply F ν hfin hν (Pi.single i 1) s hs
    change form (fun i j => entryMeasure ν hfin i j s) (Pi.single i 1) (Pi.single i 1) = _ at h
    rwa [form_single_single] at h
  have hNotTop (i : ι) (_ : i ∈ Finset.univ) : ν (Pi.single i 1) s ≠ ⊤ := by
    letI := hfin (Pi.single i 1)
    exact (measure_lt_top _ _).ne
  change (∑ i, entryMeasure ν hfin i i s) = _
  simp only [hDiag, traceMeasure, measureReal_def, Measure.finset_sum_apply]
  rw [ENNReal.toReal_sum hNotTop, Complex.ofReal_sum]

theorem entryMeasure_absolutelyContinuous_of_representation
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (ν : (ι → ℂ) → Measure X)
    (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v) (i j : ι) :
    entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hnull
  exact entryMeasure_apply_eq_zero_of_traceMeasure_null F ν hfin hν s hs hnull i j

variable [T2Space X] [LocallyCompactSpace X]

/-- Dense square positivity of the constant-vector compressions gives
genuine ordered complex measures for this same family of functionals.
The complex entry integrals are written as the four polarized integrals
against the finite positive compression measures. -/
theorem exists_positiveMatrixMeasure_of_dense_square_positive
    (F : ι → ι → C(X, ℂ) →L[ℂ] ℂ) (D : Set C(X, ℂ)) (hD : Dense D)
    (h : ∀ (v : ι → ℂ) (f : C(X, ℂ)), f ∈ D →
      0 ≤ (scalarCompression F v (star f * f)).re ∧
        (scalarCompression F v (star f * f)).im = 0) :
    ∃ ν : (ι → ℂ) → Measure X, ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
      (∀ v, (ν v).Regular) ∧
      (∀ v f, (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v) ∧
      (∀ i j (f : C(X, ℂ)), F i j f = ∑ k, weights k * (∫ x, f x ∂ν (basisTests i j k))) ∧
      (∀ v (s : Set X), MeasurableSet s →
        quadratic (fun i j => entryMeasure ν hfin i j s) v = ((ν v).real s : ℂ)) ∧
      (∀ s : Set X, MeasurableSet s →
        Matrix.PosSemidef (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ)) ∧
      IsFiniteMeasure (traceMeasure ν) ∧
      (∀ s : Set X, MeasurableSet s →
        Matrix.trace (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ) =
          ((traceMeasure ν).real s : ℂ)) ∧
      (∀ i j, entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure) ∧
      (∀ s : Set X, MeasurableSet s → traceMeasure ν s = 0 → ∀ i j, entryMeasure ν hfin i j s = 0) := by
  obtain ⟨ν, hν⟩ := exists_quadratic_measures_of_dense_square_positive F D hD h
  let hfin (v : ι → ℂ) : IsFiniteMeasure (ν v) := (hν v).2.1
  have hrep (v : ι → ℂ) (f : C(X, ℂ)) :
      (∫ x, f x ∂ν v) = quadratic (testMatrix F f) v := (hν v).2.2 f
  exact ⟨ν, hfin, (fun v => (hν v).1), hrep,
    entryFunctional_eq_integral_polarization F ν hrep,
    quadratic_entryMeasure_apply F ν hfin hrep,
    entryMeasure_posSemidef F ν hfin hrep,
    traceMeasure_isFinite_of_finite_compressions ν hfin,
    entryMeasure_trace_apply F ν hfin hrep,
    entryMeasure_absolutelyContinuous_of_representation F ν hfin hrep,
    entryMeasure_apply_eq_zero_of_traceMeasure_null F ν hfin hrep⟩

end Burnett.Microlocal.MatrixMeasureAssembly
