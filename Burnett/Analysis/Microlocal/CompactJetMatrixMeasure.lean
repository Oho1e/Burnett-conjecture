import Burnett.Analysis.Microlocal.OrderedCompactFunctionals
import Burnett.Analysis.Microlocal.MatrixMeasure.Representation

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.CompactChartMatrixMeasure

open MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open Burnett.Microlocal.CompactFunctionalProducer Burnett.Microlocal.CompactOrderedFunctional
open Burnett.Microlocal.DenseComplexFunctional Burnett.Microlocal.MatrixMeasureAssembly
open Burnett.Microlocal.MatrixPolarization
open Burnett.Analysis.LocalHminusFourier (sourceSchwartz)
open scoped InnerProduct BigOperators ContDiff Topology ComplexOrder Matrix

/-- The actual compact chart product with its induced metric and Borel structures. -/
abbrev Chart (K : BallData) := K.Point × UnitSphere

theorem traceMeasure_isFinite {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : BallData) (ν : (ι → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    IsFiniteMeasure (traceMeasure ν) := by
  refine ⟨?_⟩
  rw [traceMeasure, Measure.finset_sum_apply]
  apply ENNReal.sum_lt_top.mpr
  intro i _
  letI := hfin (Pi.single i 1)
  exact measure_lt_top _ _

theorem entryMeasure_absolutelyContinuous_trace {ι : Type} [Fintype ι] [DecidableEq ι]
    (K : BallData) (F : ι → ι → (TestSpace K →L[ℂ] ℂ))
    (ν : (ι → ℂ) → Measure (Chart K)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hν : ∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v)
    (i j : ι) :
    entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure := by
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hnull
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hnull
  exact entryMeasure_apply_eq_zero_of_traceMeasure_null F ν hfin hν s hs hnull i j

theorem complexMeasure_signedParts_absolutelyContinuous {X : Type*} [MeasurableSpace X]
    (μ : ComplexMeasure X) (τ : Measure X) (h : μ ≪ᵥ τ.toENNRealVectorMeasure) :
    ComplexMeasure.re μ ≪ᵥ τ.toENNRealVectorMeasure ∧
      ComplexMeasure.im μ ≪ᵥ τ.toENNRealVectorMeasure := by
  constructor
  · intro s hs
    rw [ComplexMeasure.re_apply, VectorMeasure.mapRange_apply, h hs, map_zero]
  · intro s hs
    rw [ComplexMeasure.im_apply, VectorMeasure.mapRange_apply, h hs, map_zero]

/-- Actual compact-chart complex matrix entries, represented by the polarized integrals of
regular positive compression measures. All list limits use one common strict subsequence. -/
theorem exists_compactChartMatrixMeasure_of_localized_weak_zero {ι : Type}
    [Fintype ι] [DecidableEq ι]
    (K : BallData) (f : ℕ → ι → Space → ℝ) (hs : ∀ n c, ContDiff ℝ ∞ (f n c))
    (hf : ∀ n c, MemLp (f n c) 2 (volume : Measure Space))
    (χ₀ : Burnett.X02.SobolevTestJet.D)
    (hχ₀ : ∀ n c x, f n c x ≠ 0 → (χ₀ : Space → ℝ) x = 1)
    (hKf : ∀ n c x, f n c x ≠ 0 → x ∈ K.closedBall)
    (B : ℝ) (hB : ∀ n c, ‖(hf n c).toLp (f n c)‖ ≤ B)
    (ht : ∀ (c : ι) (φ : Burnett.X02.SobolevTestJet.D),
      Tendsto (fun n => ∫ x, f n c x * (φ : Space → ℝ) x) atTop (𝓝 0)) :
    let u (n : ℕ) (c : ι) := (sourceSchwartz (hs n c) χ₀ (hχ₀ n c)).toLp 2 volume
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ F : ι → ι → (TestSpace K →L[ℂ] ℂ),
      ∃ ν : (ι → ℂ) → Measure (Chart K),
      ∃ hfin : ∀ v, IsFiniteMeasure (ν v),
        (∀ v, (ν v).Regular) ∧
        (∀ v q, (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v) ∧
        (∀ i j q, F i j q = ∑ k, weights k * (∫ x, q x ∂ν (basisTests i j k))) ∧
        (∀ ps i j, let q := separableRestriction K ps
          Tendsto (fun n => inner ℂ (u (σ n) i) (listOperator K ps (u (σ n) j)))
            atTop (𝓝 (∑ k, weights k * (∫ x, q x ∂ν (basisTests i j k))))) ∧
        (∀ v (s : Set (Chart K)), MeasurableSet s →
          quadratic (fun i j => entryMeasure ν hfin i j s) v = ((ν v).real s : ℂ)) ∧
        (∀ s : Set (Chart K), MeasurableSet s →
          Matrix.PosSemidef (fun i j => entryMeasure ν hfin i j s : Matrix ι ι ℂ)) ∧
        IsFiniteMeasure (traceMeasure ν) ∧
        (∀ i j, entryMeasure ν hfin i j ≪ᵥ (traceMeasure ν).toENNRealVectorMeasure) := by
  intro u
  obtain ⟨σ, hσ, F, hPair, _, _, hPos⟩ :=
    exists_commonCompactMatrixFunctional_positive K f hs hf χ₀ hχ₀ hKf B hB ht
  obtain ⟨ν, hν⟩ := exists_quadratic_measures_of_dense_square_positive F
    (Set.range (separableRestriction K)) (separableRestriction_dense K) (by
      intro v q hq
      obtain ⟨ps, rfl⟩ := hq
      rw [scalarCompression_apply]
      exact hPos v ps)
  let hfin (v : ι → ℂ) : IsFiniteMeasure (ν v) := (hν v).2.1
  have hrep (v : ι → ℂ) (q : TestSpace K) :
      (∫ x, q x ∂ν v) = quadratic (testMatrix F q) v := (hν v).2.2 q
  have hEntry := entryFunctional_eq_integral_polarization F ν hrep
  refine ⟨σ, hσ, F, ν, hfin, (fun v => (hν v).1), hrep, hEntry, ?_,
    quadratic_entryMeasure_apply F ν hfin hrep,
    entryMeasure_posSemidef F ν hfin hrep,
    traceMeasure_isFinite K ν hfin, entryMeasure_absolutelyContinuous_trace K F ν hfin hrep⟩
  intro ps i j
  dsimp only
  rw [← hEntry i j (separableRestriction K ps)]
  exact hPair ps i j

end Burnett.Microlocal.CompactChartMatrixMeasure
