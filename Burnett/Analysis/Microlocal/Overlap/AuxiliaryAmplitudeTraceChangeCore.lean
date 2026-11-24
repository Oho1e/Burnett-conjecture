import Burnett.Analysis.Microlocal.Overlap.CompactAmplitudeAuxiliarySectionChange
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryTraceReconstruction
import Burnett.Analysis.Microlocal.Overlap.GlobalAmplitudeEntryMeasure

set_option autoImplicit false
set_option maxRecDepth 3000
set_option maxHeartbeats 720000

noncomputable section
namespace Burnett.Microlocal.Overlap

open MeasureTheory Burnett.Geometry Burnett.RicciSymbol
open ConnectionDifference ManifoldMetric ManifoldBilinear
open ContravariantTensor (tensorTangentBasis)
open UnitCosphere (Cosphere projection)
open CotangentAngularExtension (cotangentNormalize_projection)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity AmplitudeFiber)
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.F07.IntrinsicAmplitude
  (auxiliaryTraceInBasis auxiliaryTraceInBasis_eq auxiliaryTraceLinear
    auxiliaryTraceLinear_nonneg_and_eq_zero_iff auxiliaryTrace_normalization_preserves_positive_contraction
    chartAmplitudeTangentBasis orderedChartAmplitudeComponents)
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor)
open scoped ComplexOrder ContDiff ENNReal Manifold

open Burnett.F07.IntrinsicAmplitude (chartInverse_entries)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem renormalizeUnitCosphere_projection (r r' : Metric (M := M)) (p : Cosphere r) :
    projection (renormalizeUnitCosphere r r' p) = projection p :=
  cotangentNormalize_projection r' p.val

/-- The trace for the new metric, applied at the base point of an old unit ray. -/
def intrinsicAmplitudeTraceInMetric (r r' : Metric (M := M)) (D : AmplitudeCovarianceDensity r)
    (p : Cosphere r) : ℝ :=
  let x := projection p
  let b := tensorTangentBasis x x (mem_chart_source CoordinateSpace x)
  auxiliaryTraceInBasis b
    (inverseMetricTensor r'.inner (GlobalLeviCivita.inner_nondegenerate r') x) (D p)

theorem intrinsicAmplitudeTraceInMetric_eq_chart (r r' : Metric (M := M)) (q : CompactChartInput M)
    (D : AmplitudeCovarianceDensity r) (z : Chart q.ball) :
    intrinsicAmplitudeTraceInMetric r r' D (chartAuxiliaryCosphere r q z) =
      auxiliaryTraceLinear (chartAuxiliaryInverse r' q z.1) (orderedChartAmplitudeComponents r q D z) := by
  unfold intrinsicAmplitudeTraceInMetric
  rw [auxiliaryTraceInBasis_eq _ (chartAmplitudeTangentBasis r q z)]
  have hR : (fun i j => inverseMetricTensor r'.inner (GlobalLeviCivita.inner_nondegenerate r')
      (projection (chartAuxiliaryCosphere r q z)) ((chartAmplitudeTangentBasis r q z).dualBasis i)
        ((chartAmplitudeTangentBasis r q z).dualBasis j)) = chartAuxiliaryInverse r' q z.1 := by
    funext i j
    exact chartInverse_entries r r'.inner r'.symm (GlobalLeviCivita.inner_nondegenerate r') q z i j
  exact congrArg (fun R : Tensor2 => auxiliaryTraceLinear R (orderedChartAmplitudeComponents r q D z)) hR

/-- Read the new-section density at the old direction in the same tensor fiber. -/
def pullbackAmplitudeDensity (r r' : Metric (M := M))
    (D : AmplitudeCovarianceDensity r') : AmplitudeCovarianceDensity r :=
  fun p => cast (congrArg (fun x : M => AmplitudeFiber x) (renormalizeUnitCosphere_projection r r' p))
    (D (renormalizeUnitCosphere r r' p))

variable {X : Type*} [MeasurableSpace X]

/-- Relative to the old trace control, the next control gains the radial
weight times the new trace of the old normalized covariance. Both traces
are strictly positive almost everywhere on the old control. -/
theorem auxiliaryTrace_normalization_change_control (μ : Measure X) (R R' : X → Tensor2)
    (A : X → Matrix Pair Pair ℂ) (s : X → ℝ)
    (hPositive : ∀ᵐ p ∂μ, Matrix.PosDef (R p) ∧ Matrix.PosDef (R' p) ∧ (A p).PosSemidef)
    (hT : AEMeasurable (fun p => auxiliaryTraceLinear (R p) (A p)) μ)
    (hT' : AEMeasurable (fun p => auxiliaryTraceLinear (R' p) (A p)) μ)
    (hs : AEMeasurable s μ) (hs₀ : ∀ᵐ p ∂μ, 0 ≤ s p) :
    let a (p : X) := auxiliaryTraceLinear (R p) (A p)
    let b (p : X) := auxiliaryTraceLinear (R' p) (A p)
    let τ := μ.withDensity (fun p => ENNReal.ofReal (a p))
    let t (p : X) := (a p)⁻¹ * b p
    AEMeasurable t μ ∧
      (∀ᵐ p ∂τ, 0 < a p ∧ 0 < b p) ∧
      μ.withDensity (fun p => ENNReal.ofReal (s p * b p)) =
        τ.withDensity (fun p => ENNReal.ofReal (s p) * ENNReal.ofReal (t p)) := by
  intro a b τ t
  have hMeas : AEMeasurable t μ := hT.inv.mul hT'
  have hPos : ∀ᵐ p ∂τ, 0 < a p ∧ 0 < b p := by
    apply (ae_withDensity_iff' (ENNReal.measurable_ofReal.comp_aemeasurable hT)).mpr
    filter_upwards [hPositive] with p hp hNonzero
    have ha : 0 < a p := by
      change ENNReal.ofReal (a p) ≠ 0 at hNonzero
      rwa [ne_eq, ENNReal.ofReal_eq_zero, not_le] at hNonzero
    have hA : A p ≠ 0 := fun hA => ha.ne'
      ((auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R p) hp.1 (A p) hp.2.2).2.mpr hA)
    have hB := auxiliaryTraceLinear_nonneg_and_eq_zero_iff (R' p) hp.2.1 (A p) hp.2.2
    exact ⟨ha, lt_of_le_of_ne hB.1 (fun h => hA (hB.2.mp h.symm))⟩
  let L (p : X) := s p • auxiliaryTraceLinear (R' p)
  have hL : AEMeasurable (fun p => L p (A p)) μ := hs.mul hT'
  have hOld : ∀ᵐ p ∂μ, Matrix.PosDef (R p) ∧ (A p).PosSemidef :=
    hPositive.mono (fun _ hp => ⟨hp.1, hp.2.2⟩)
  have hEq := auxiliaryTrace_normalization_preserves_positive_contraction
    μ R A hOld hT L hL Set.univ MeasurableSet.univ
  simp only [Measure.restrict_univ] at hEq
  refine ⟨hMeas, hPos, hEq.symm.trans (withDensity_congr_ae ?_)⟩
  filter_upwards [(withDensity_absolutelyContinuous μ (fun p => ENNReal.ofReal (a p))).ae_le hs₀]
    with p hp
  change ENNReal.ofReal (s p * auxiliaryTraceLinear (R' p) ((a p)⁻¹ • A p)) =
    ENNReal.ofReal (s p) * ENNReal.ofReal (t p)
  rw [map_smul, smul_eq_mul, ENNReal.ofReal_mul hp]

end Burnett.Microlocal.Overlap
