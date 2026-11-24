import Burnett.Analysis.Microlocal.Overlap.CotangentPhysicalJetMeasure

/-! Weight a single original chart by its own inverse cutoff square. -/

set_option autoImplicit false
set_option maxHeartbeats 150000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.Geometry.UnitNullCompactness (CotangentBundle cotangentUnitNull)
open Burnett.Geometry.CotangentAngularExtension (isClosed_cotangentUnitNull)
open Burnett.F05.ActualChartAuxiliarySection (chartAuxiliaryRay continuous_chartAuxiliaryRay)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (JetSlot)
open scoped ContDiff Manifold ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]
variable (q : CompactChartInput M)

def chartInverseCutoffSquare (z : Chart q.ball) : ℝ≥0∞ :=
  ENNReal.ofReal ((((q.cutoff : CoordinateSpace → ℝ) z.1)⁻¹) ^ 2)

variable [IsManifold Model ∞ M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

variable (r : Metric (M := M)) (B : Field (M := M)) (hn : IsNondegenerate B)
variable (ν : (JetSlot → ℂ) → Measure (Chart q.ball)) (hfin : ∀ v, IsFiniteMeasure (ν v))

/-- The physical chart measure divided by its original cutoff squared and
pushed along the actual auxiliary-unit cotangent map. -/
def normalizedCotangentPhysicalMeasure : Measure (CotangentBundle M) :=
  ((chartPhysicalJetMeasure r B hn q ν hfin).withDensity (chartInverseCutoffSquare q)).map
    (chartAuxiliaryRay r q)

/-- The normalized measure is finite on Borel sets where the original cutoff
is bounded away from zero along the chart map. -/
theorem normalizedCotangentPhysicalMeasure_lt_top_of_cutoff_lower_bound
    (hB : IsSmooth B) {S : Set (CotangentBundle M)} (hS : MeasurableSet S)
    {δ : ℝ} (hδ : 0 < δ)
    (hLower : ∀ z : Chart q.ball, chartAuxiliaryRay r q z ∈ S →
      δ ≤ |(q.cutoff : CoordinateSpace → ℝ) z.1|) :
    normalizedCotangentPhysicalMeasure q r B hn ν hfin S < ⊤ := by
  let μ := chartPhysicalJetMeasure r B hn q ν hfin
  let A := chartAuxiliaryRay r q ⁻¹' S
  let C := ENNReal.ofReal ((δ⁻¹) ^ 2)
  letI : IsFiniteMeasure μ := isFiniteMeasure_chartPhysicalJetMeasure r B hB hn q ν hfin
  have hRay := (continuous_chartAuxiliaryRay r q).measurable
  have hA : MeasurableSet A := hRay hS
  have hLe : chartInverseCutoffSquare q ≤ᵐ[μ.restrict A] fun _ => C := by
    filter_upwards [ae_restrict_mem (μ := μ) hA] with z hz
    have hinv := inv_anti₀ hδ (hLower z hz)
    apply ENNReal.ofReal_le_ofReal
    rw [← sq_abs (((q.cutoff : CoordinateSpace → ℝ) z.1)⁻¹), abs_inv]
    exact pow_le_pow_left₀ (inv_nonneg.mpr (abs_nonneg _)) hinv 2
  rw [normalizedCotangentPhysicalMeasure, Measure.map_apply hRay hS, withDensity_apply _ hA]
  calc
    (∫⁻ z in A, chartInverseCutoffSquare q z ∂μ) ≤ ∫⁻ _ in A, C ∂μ := lintegral_mono_ae hLe
    _ = C * μ A := by simp only [lintegral_const, Measure.restrict_apply_univ]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top (measure_lt_top μ A)

theorem normalizedCotangentPhysicalMeasure_compl_null
    (hB : IsSmooth B) (hsB : IsSymmetric B) :
    normalizedCotangentPhysicalMeasure q r B hn ν hfin (cotangentUnitNull r B hn)ᶜ = 0 := by
  have hRay := (continuous_chartAuxiliaryRay r q).measurable
  have hZ := (isClosed_cotangentUnitNull r B hB hn hsB).measurableSet.compl
  have h0 := cotangentPhysicalJetMeasure_compl_null r B hn q ν hfin hB hsB
  rw [cotangentPhysicalJetMeasure, Measure.map_apply hRay hZ] at h0
  rw [normalizedCotangentPhysicalMeasure, Measure.map_apply hRay hZ]
  exact withDensity_absolutelyContinuous _ _ h0

end Burnett.Microlocal.Overlap
