import Burnett.Analysis.Microlocal.CurlCovariance
import Burnett.Analysis.Microlocal.CompactJetMatrixDensity

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.FixedChartGeometricDensity

open MeasureTheory Filter Set Matrix Burnett.RicciSymbol
open Burnett.Microlocal.CurlDensity
open Burnett.Microlocal.CompactChartMatrixMeasure (Chart)
open Burnett.Microlocal.SmoothAngularTests Burnett.Microlocal.SmoothBaseTests
open scoped InnerProduct BigOperators ComplexOrder Matrix

/-- The covector underlying the actual round frequency sphere in the chart product. -/
def roundCovector {K : BallData} (z : Chart K) : Covector :=
  fun a => (z.2 : Space) a

theorem roundCovector_dual_pairing {K : BallData} (z : Chart K) :
    ∑ a, roundCovector z a * roundCovector z a = 1 := by
  have hz : ‖(z.2 : Space)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using z.2.property
  calc
    _ = ∑ a, ‖(z.2 : Space) a‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Real.norm_eq_abs, sq_abs, pow_two]
      rfl
    _ = ‖(z.2 : Space)‖ ^ 2 := (EuclideanSpace.norm_sq_eq (z.2 : Space)).symm
    _ = 1 := by rw [hz, one_pow]

open Burnett.Microlocal.MatrixTraceDensity

/-- The common chart's covariant jet matrix, in physical covariance orientation. -/
def chartPhysicalCovariance (K : BallData) (ν : (JetSlot → ℂ) → Measure (Chart K))
    (hfin : ∀ v, IsFiniteMeasure (ν v)) (x : Chart K) : Matrix JetSlot JetSlot ℂ :=
  (density ν hfin x)ᵀ


end Burnett.Microlocal.FixedChartGeometricDensity
