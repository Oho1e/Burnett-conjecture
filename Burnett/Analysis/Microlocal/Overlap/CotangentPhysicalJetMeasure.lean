import Burnett.Analysis.Microlocal.Overlap.ChartPhysicalJetMeasure

/-! Push a chart's physical measure to the actual unit cotangent rays. -/

set_option autoImplicit false
set_option maxHeartbeats 220000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension (isClosed_cotangentUnitNull)
open Burnett.F05.ActualChartAuxiliarySection
  (chartAuxiliaryRay chartAuxiliaryRay_unit continuous_chartAuxiliaryRay)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open Burnett.Microlocal.MatrixMeasureAssembly (traceMeasure)
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

variable (r : Metric (M := M)) (B : Field (M := M))
variable (hn : IsNondegenerate B) (q : CompactChartInput M)
variable (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))

/-- The original chart's physical measure on the actual cotangent bundle. -/
def cotangentPhysicalJetMeasure : Measure (CotangentBundle M) :=
  (chartPhysicalJetMeasure r B hn q ν hfin).map (chartAuxiliaryRay r q)

omit [BorelSpace (CotangentBundle M)] in
theorem isFiniteMeasure_cotangentPhysicalJetMeasure (hB : IsSmooth B) :
    IsFiniteMeasure (cotangentPhysicalJetMeasure r B hn q ν hfin) := by
  letI := isFiniteMeasure_chartPhysicalJetMeasure r B hB hn q ν hfin
  exact Measure.isFiniteMeasure_map _ _

theorem cotangentPhysicalJetMeasure_compl_null (hB : IsSmooth B) (hsB : IsSymmetric B) :
    cotangentPhysicalJetMeasure r B hn q ν hfin (cotangentUnitNull r B hn)ᶜ = 0 := by
  have hPreimage : chartAuxiliaryRay r q ⁻¹' (cotangentUnitNull r B hn)ᶜ =
      (chartAuxiliaryNull r B hn q)ᶜ := by
    ext p
    simp only [mem_preimage, mem_compl_iff, cotangentUnitNull, chartAuxiliaryNull, mem_setOf_eq,
      chartAuxiliaryRay_unit r q p, true_and]
  rw [cotangentPhysicalJetMeasure, Measure.map_apply (continuous_chartAuxiliaryRay r q).measurable
    (isClosed_cotangentUnitNull r B hB hn hsB).measurableSet.compl, hPreimage]
  exact chartPhysicalJetMeasure_compl_null r B hB hsB hn q ν hfin

theorem cotangentPhysicalJetMeasure_apply_eq_setIntegral (hB : IsSmooth B)
    (hPos : ∀ᵐ z ∂(traceMeasure ν).restrict (chartAuxiliaryNull r B hn q),
      0 ≤ (chartPhysicalJetContraction r B q ν hfin z).re ∧
        (chartPhysicalJetContraction r B q ν hfin z).im = 0)
    {S : Set (CotangentBundle M)} (hS : MeasurableSet S) :
    (((cotangentPhysicalJetMeasure r B hn q ν hfin) S).toReal : ℂ) =
      ∫ z in (chartAuxiliaryRay r q ⁻¹' S) ∩ chartAuxiliaryNull r B hn q,
        chartPhysicalJetContraction r B q ν hfin z ∂traceMeasure ν := by
  have hr := (continuous_chartAuxiliaryRay r q).measurable
  rw [cotangentPhysicalJetMeasure, Measure.map_apply hr hS]
  exact chartPhysicalJetMeasure_apply_eq_setIntegral r B hB hn q ν hfin hPos (hr hS)

end Burnett.Microlocal.Overlap
