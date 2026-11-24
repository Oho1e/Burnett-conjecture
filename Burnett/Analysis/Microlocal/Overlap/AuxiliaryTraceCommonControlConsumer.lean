import Burnett.Analysis.Microlocal.Overlap.ChartAmplitudeContractions
import Burnett.Analysis.Microlocal.Overlap.AmplitudeDensityOnCommonControl

/-! Use the auxiliary trace to normalize the same covariance on a common control measure. -/

set_option autoImplicit false
set_option maxHeartbeats 420000

noncomputable section

namespace Burnett.F07.IntrinsicAmplitude

open Matrix MeasureTheory Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.Microlocal.Overlap (ae_eq_amplitudeDensities_on_sum normalization_agrees_on_common_control)
open Burnett.Geometry.UnitCosphere (Cosphere projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open scoped BigOperators ContDiff Manifold

variable {X : Type*} [MeasurableSpace X]

theorem aemeasurable_auxiliaryTraceLinear (μ : Measure X) (R : X → Tensor2)
    (A : X → Matrix Pair Pair ℂ) (hR : ∀ i j, AEMeasurable (fun x => R x i j) μ)
    (hA : ∀ i j, AEMeasurable (fun x => A x i j) μ) :
    AEMeasurable (fun x => auxiliaryTraceLinear (R x) (A x)) μ := by
  simp only [auxiliaryTraceLinear_apply]
  refine Finset.aemeasurable_fun_sum _ (fun i _ => Finset.aemeasurable_fun_sum _ (fun j _ => ?_))
  exact ((hR i.1 j.1).mul (hR i.2 j.2)).mul
    (Complex.continuous_re.measurable.comp_aemeasurable (hA i j))

/-- The common control comparison with the same real-linear auxiliary trace at every phase point. -/
theorem normalization_agrees_on_common_auxiliary_control
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (R : X → Tensor2) (A B : X → Matrix Pair Pair ℂ)
    (hR : ∀ i j, AEMeasurable (fun x => R x i j) (μ + ν))
    (hA : ∀ i j, AEMeasurable (fun x => A x i j) (μ + ν))
    (hB : ∀ i j, AEMeasurable (fun x => B x i j) (μ + ν))
    (hab : (fun x => (μ.rnDeriv (μ + ν) x).toReal • A x)
      =ᵐ[μ + ν] fun x => (ν.rnDeriv (μ + ν) x).toReal • B x) :
    let τ := μ.withDensity (fun x => ENNReal.ofReal (auxiliaryTraceLinear (R x) (A x)))
    τ = ν.withDensity (fun x => ENNReal.ofReal (auxiliaryTraceLinear (R x) (B x))) ∧
      (fun x => (auxiliaryTraceLinear (R x) (A x))⁻¹ • A x)
        =ᵐ[τ] fun x => (auxiliaryTraceLinear (R x) (B x))⁻¹ • B x :=
  normalization_agrees_on_common_control μ ν A B (fun x => auxiliaryTraceLinear (R x))
    (aemeasurable_auxiliaryTraceLinear (μ + ν) R A hR hA)
    (aemeasurable_auxiliaryTraceLinear (μ + ν) R B hR hB) hab

/-- Equality of all original complex entry integrals yields the same auxiliary
control and the same trace-normalized density. -/
theorem normalization_agrees_on_common_auxiliary_control_of_entry_integrals
    (μ ν : Measure X) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (R : X → Tensor2) (A B : X → Matrix Pair Pair ℂ)
    (hR : ∀ i j, AEMeasurable (fun x => R x i j) (μ + ν))
    (hA : ∀ i j, AEMeasurable (fun x => A x i j) (μ + ν))
    (hB : ∀ i j, AEMeasurable (fun x => B x i j) (μ + ν))
    (hIntA : ∀ i j, Integrable (fun x => A x i j) μ)
    (hIntB : ∀ i j, Integrable (fun x => B x i j) ν)
    (hEqual : ∀ i j (s : Set X), MeasurableSet s →
      (∫ x in s, A x i j ∂μ) = ∫ x in s, B x i j ∂ν) :
    let τ := μ.withDensity (fun x => ENNReal.ofReal (auxiliaryTraceLinear (R x) (A x)))
    τ = ν.withDensity (fun x => ENNReal.ofReal (auxiliaryTraceLinear (R x) (B x))) ∧
      (fun x => (auxiliaryTraceLinear (R x) (A x))⁻¹ • A x)
        =ᵐ[τ] fun x => (auxiliaryTraceLinear (R x) (B x))⁻¹ • B x :=
  normalization_agrees_on_common_auxiliary_control μ ν R A B hR hA hB
    (ae_eq_amplitudeDensities_on_sum μ ν A B hIntA hIntB hEqual)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem measurable_chartAuxiliaryInverse_entries (r : Metric (M := M))
    (q : CompactChartInput M) (i j : Index) :
    Measurable (fun z : Chart q.ball => chartAuxiliaryInverse r q z.1 i j) :=
  ((continuous_apply j).comp ((continuous_apply i).comp
    ((continuous_chartAuxiliaryInverse r q).comp continuous_fst))).measurable

/-- In a genuine compact chart the common trace uses the actual continuous inverse entries. -/
theorem normalization_agrees_on_common_chart_auxiliary_control
    (r : Metric (M := M)) (q : CompactChartInput M)
    (μ ν : Measure (Chart q.ball)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (A B : Chart q.ball → Matrix Pair Pair ℂ)
    (hA : ∀ i j, AEMeasurable (fun z => A z i j) (μ + ν))
    (hB : ∀ i j, AEMeasurable (fun z => B z i j) (μ + ν))
    (hab : (fun z => (μ.rnDeriv (μ + ν) z).toReal • A z)
      =ᵐ[μ + ν] fun z => (ν.rnDeriv (μ + ν) z).toReal • B z) :
    let τ := μ.withDensity (fun z => ENNReal.ofReal (auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) (A z)))
    τ = ν.withDensity (fun z => ENNReal.ofReal (auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) (B z))) ∧
      (fun z => (auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) (A z))⁻¹ • A z)
        =ᵐ[τ] fun z => (auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) (B z))⁻¹ • B z :=
  normalization_agrees_on_common_auxiliary_control μ ν (fun z => chartAuxiliaryInverse r q z.1) A B
    (fun i j => (measurable_chartAuxiliaryInverse_entries r q i j).aemeasurable) hA hB hab

end Burnett.F07.IntrinsicAmplitude
