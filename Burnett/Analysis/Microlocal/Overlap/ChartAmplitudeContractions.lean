import Burnett.Analysis.Microlocal.Overlap.IntrinsicAmplitudeContractions
import Burnett.Analysis.Microlocal.ChartAuxiliaryEmbedding
import Burnett.Analysis.Microlocal.CoordinateRicciPrincipalRow
import Burnett.Analysis.Microlocal.PhysicalDensity

/-! The intrinsic scalar contractions in the original preferred chart. -/

set_option autoImplicit false
set_option maxHeartbeats 750000

noncomputable section
namespace Burnett.F07.IntrinsicAmplitude

open Module Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric
open Burnett.Geometry.ContravariantTensor
open Burnett.Geometry.IntrinsicScalarEinstein (inverseMetricTensor inverseMetricTensor_components)
open Burnett.Geometry.UnitCosphere (projection)
open Burnett.F07.IntrinsicAmplitudeCoordinates (AmplitudeCovarianceDensity)
open Burnett.F05.ActualChartAuxiliarySection
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.Microlocal.CurlDensity (Pair)
open Burnett.Microlocal.PhysicalDensity (physicalCoefficient physicalContraction)
open Burnett.Microlocal.RicciRow (backgroundInverse)
open scoped BigOperators ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The genuine tangent basis at the base point of the auxiliary ray. -/
def chartAmplitudeTangentBasis (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) : Basis Index ℝ (TangentSpace Model (projection (chartAuxiliaryCosphere r q z))) :=
  tensorTangentBasis q.center _
    ((chartAt CoordinateSpace q.center).symm_mapsTo (q.ball_in_chart z.1.property))

/-- Components of an actual four-slot density, in ordered pairs and with their complex values intact. -/
def orderedChartAmplitudeComponents (r : Metric (M := M)) (q : CompactChartInput M)
    (J : AmplitudeCovarianceDensity r) (z : Chart q.ball) : Matrix Pair Pair ℂ :=
  let b := chartAmplitudeTangentBasis r q z
  fun i j => J (chartAuxiliaryCosphere r q z) ![b i.1, b i.2, b j.1, b j.2]

theorem chartInverse_entries
    (r : Metric (M := M)) (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (q : CompactChartInput M) (z : Chart q.ball) (i j : Index) :
    let x := projection (chartAuxiliaryCosphere r q z)
    let b := chartAmplitudeTangentBasis r q z
    inverseMetricTensor B hn x (b.dualBasis i) (b.dualBasis j) = backgroundInverse B q.center z.1 i j := by
  let e := chartAt CoordinateSpace q.center
  let x := projection (chartAuxiliaryCosphere r q z)
  have ht := q.ball_in_chart z.1.property
  have hx : x ∈ e.source := e.symm_mapsTo ht
  change inverseMetricTensor B hn x ((tensorTangentBasis q.center x hx).dualBasis i)
    ((tensorTangentBasis q.center x hx).dualBasis j) = _
  rw [← contravariantComponents_chart (inverseMetricTensor B hn) q.center x hx,
    inverseMetricTensor_components B hn hs q.center x hx]
  change backgroundInverse B q.center (e x) i j = _
  rw [show e x = (z.1 : CoordinateSpace) from e.right_inv ht]

private theorem physicalCoefficient_mul_re (G : Tensor2) (A : ℂ) (i j : Pair) :
    (physicalCoefficient G i j * A).re =
      (G i.1 j.1 * G i.2 j.2 - G i.1 i.2 * G j.1 j.2 / 2) * A.re := by
  have h : physicalCoefficient G i j =
      ((G i.1 j.1 * G i.2 j.2 - G i.1 i.2 * G j.1 j.2 / 2 : ℝ) : ℂ) := by
    simp only [physicalCoefficient, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [h]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

private theorem quarter_mul_re (c : ℂ) : ((1 / 4 : ℂ) * c).re = c.re / 4 := by
  rw [show (1 / 4 : ℂ) = ((1 / 4 : ℝ) : ℂ) by norm_num]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The intrinsic physical weight is the quarter contraction of the actual complex chart components. -/
theorem intrinsicPhysicalWeight_eq_chart
    (r : Metric (M := M)) (B : Field (M := M)) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (q : CompactChartInput M) (J : AmplitudeCovarianceDensity r) (z : Chart q.ball) :
    intrinsicPhysicalWeight B hn J (chartAuxiliaryCosphere r q z) =
      ((1 / 4 : ℂ) * physicalContraction (backgroundInverse B q.center z.1)
        (orderedChartAmplitudeComponents r q J z)).re := by
  rw [intrinsicPhysicalWeight_eq_basis B hn J _ (chartAmplitudeTangentBasis r q z)]
  simp only [quarterContractionInBasis, chartInverse_entries r B hs hn q z, quarter_mul_re,
    physicalContraction, Complex.re_sum, Fintype.sum_prod_type, physicalCoefficient_mul_re,
    orderedChartAmplitudeComponents]

/-- The dual-basis coefficients of the actual fiber inverse are the chart inverse of `r`. -/
theorem chartAuxiliaryInverse_eq_fiber_entries (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) (i j : Index) :
    let x := projection (chartAuxiliaryCosphere r q z)
    let b := chartAmplitudeTangentBasis r q z
    inverseMetricTensor r.inner (GlobalLeviCivita.inner_nondegenerate r) x (b.dualBasis i) (b.dualBasis j) =
      chartAuxiliaryInverse r q z.1 i j :=
  chartInverse_entries r r.inner r.symm (GlobalLeviCivita.inner_nondegenerate r) q z i j

/-- The chart trace of the ordered components is the intrinsic auxiliary trace of the same tensor. -/
theorem intrinsicAuxiliaryTrace_eq_chart (r : Metric (M := M)) (q : CompactChartInput M)
    (J : AmplitudeCovarianceDensity r) (z : Chart q.ball) :
    intrinsicAuxiliaryTrace r J (chartAuxiliaryCosphere r q z) =
      auxiliaryTraceLinear (chartAuxiliaryInverse r q z.1) (orderedChartAmplitudeComponents r q J z) := by
  rw [intrinsicAuxiliaryTrace_eq_basis r J _ (chartAmplitudeTangentBasis r q z)]
  simp only [auxiliaryTraceInBasis, auxiliaryTraceLinear_apply, orderedChartAmplitudeComponents,
    chartAuxiliaryInverse_eq_fiber_entries r q z]

theorem chartAuxiliaryInverse_posDef (r : Metric (M := M)) (q : CompactChartInput M)
    (z : Chart q.ball) : Matrix.PosDef (chartAuxiliaryInverse r q z.1) :=
  (coordinateMetric_posDef r q.center (q.ball_in_chart z.1.property)).inv

end Burnett.F07.IntrinsicAmplitude
