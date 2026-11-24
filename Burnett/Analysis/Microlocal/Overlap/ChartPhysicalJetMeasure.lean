import Burnett.Analysis.Microlocal.Overlap.PhysicalPlateauTests
import Burnett.Analysis.Microlocal.Overlap.PositiveMeasureOfComplexDensity

/-! The scalar contraction and its positive measure on an original chart. -/

set_option autoImplicit false
set_option maxHeartbeats 240000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open Burnett.Microlocal.MatrixTraceDensity (density integrable_density_entry)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

variable (r : Metric (M := M)) (B : Field (M := M)) (q : CompactChartInput M)
variable (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))

/-- The same ordered-entry contraction as in the Borel overlap theorem. -/
def chartPhysicalJetContraction (z : Chart q.ball) : ℂ :=
  ∑ i : JetSlot, ∑ j : JetSlot,
    (chartPhysicalJetWeight r B q.center z.1 i j : ℂ) * density ν hfin z i j

variable {q ν hfin}

theorem integrable_chartPhysicalJetContraction
    (hB : IsSmooth B) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    Integrable (chartPhysicalJetContraction r B q ν hfin) (traceMeasure ν) := by
  unfold chartPhysicalJetContraction
  refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun j _ => ?_
  let w (z : Chart q.ball) : ℂ := chartPhysicalJetWeight r B q.center z.1 i j
  have hw : Continuous w := continuous_chartPhysicalJetWeight r B hB hn q i j
  obtain ⟨C, hC⟩ := (isCompact_univ.image hw).isBounded.exists_norm_le
  exact (integrable_density_entry ν hfin i j).bdd_mul hw.measurable.aestronglyMeasurable
    ⟨C, fun z => hC (w z) (mem_image_of_mem w (mem_univ z))⟩

/-- Restrict the original trace to the actual auxiliary null shell and
weight it by the nonnegative real part of the scalar contraction. The
vacuum kernel will show that on the shell the contraction already has
nonnegative real values. -/
def chartPhysicalJetMeasure (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    Measure (Chart q.ball) :=
  positiveMeasureOfComplexDensity ((traceMeasure ν).restrict (chartAuxiliaryNull r B hn q))
    (chartPhysicalJetContraction r B q ν hfin)

theorem isFiniteMeasure_chartPhysicalJetMeasure
    (hB : IsSmooth B) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    IsFiniteMeasure (chartPhysicalJetMeasure r B hn q ν hfin) :=
  isFiniteMeasure_positiveMeasureOfComplexDensity
    ((integrable_chartPhysicalJetContraction r B hB hn q ν hfin).mono_measure Measure.restrict_le_self)

theorem chartPhysicalJetMeasure_compl_null
    (hB : IsSmooth B) (hsB : IsSymmetric B) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v)) :
    chartPhysicalJetMeasure r B hn q ν hfin (chartAuxiliaryNull r B hn q)ᶜ = 0 := by
  have hZ := measurableSet_chartAuxiliaryNull r B hB hsB hn q
  rw [chartPhysicalJetMeasure, positiveMeasureOfComplexDensity, withDensity_apply _ hZ.compl,
    Measure.restrict_restrict hZ.compl, compl_inter_self, Measure.restrict_empty, lintegral_zero_measure]

theorem chartPhysicalJetMeasure_apply_eq_setIntegral
    (hB : IsSmooth B) (hn : IsNondegenerate B) (q : CompactChartInput M)
    (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))
    (hPos : ∀ᵐ z ∂(traceMeasure ν).restrict (chartAuxiliaryNull r B hn q),
      0 ≤ (chartPhysicalJetContraction r B q ν hfin z).re ∧
        (chartPhysicalJetContraction r B q ν hfin z).im = 0)
    {S : Set (Chart q.ball)} (hS : MeasurableSet S) :
    (((chartPhysicalJetMeasure r B hn q ν hfin) S).toReal : ℂ) =
      ∫ z in S ∩ chartAuxiliaryNull r B hn q, chartPhysicalJetContraction r B q ν hfin z ∂traceMeasure ν := by
  have hi := (integrable_chartPhysicalJetContraction r B hB hn q ν hfin).mono_measure
    (Measure.restrict_le_self (s := chartAuxiliaryNull r B hn q))
  have h := positiveMeasureOfComplexDensity_apply_eq_setIntegral hi hPos hS
  rwa [Measure.restrict_restrict hS] at h

end Burnett.Microlocal.Overlap
