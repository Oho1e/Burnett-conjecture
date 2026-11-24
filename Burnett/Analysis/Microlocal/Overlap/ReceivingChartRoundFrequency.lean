import Burnett.Analysis.Microlocal.Overlap.ReceivingChartGeometricBridge
import Burnett.Analysis.Microlocal.Overlap.AuxiliaryRay

/-! The pointwise frequency action on the actual source round ray. -/

set_option autoImplicit false

noncomputable section
namespace Burnett.Microlocal.AtlasOverlapKernel

open Matrix Burnett.RicciSymbol Burnett.Geometry ConnectionDifference ManifoldMetric
open Burnett.Geometry.ChartVolume (derivativeMatrix)
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.F07.IntrinsicAmplitudeCoordinates (fixedCotangentTransitionMatrix)
open scoped Manifold Matrix

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

private theorem derivativeMatrix_adjoint_real (L : E →L[ℝ] E) :
    derivativeMatrix L.adjoint = (derivativeMatrix L)ᵀ := by
  let b := EuclideanSpace.basisFun Index ℝ
  have h := LinearMap.toMatrix_adjoint b b L.toLinearMap
  change derivativeMatrix L.adjoint = (derivativeMatrix L)ᴴ at h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The Fourier frequency is exactly the matrix product used in the
receiving coordinate phase. This holds before normalizing the direction. -/
theorem receivingFrequency_eq_fixedCotangentTransition_mulVec (c d : AtlasChart M)
    {x : M} (hc : x ∈ c.chart.source) (ξ : E) :
    receivingFrequency c d (c.chart x) ξ =
      WithLp.toLp 2 (fixedCotangentTransitionMatrix c d x *ᵥ (fun i : Index => ξ i)) := by
  let L := receivingFrequency c d (c.chart x)
  have h := LinearMap.toMatrix_mulVec_repr coordinateBasis coordinateBasis L.toLinearMap ξ
  change derivativeMatrix L *ᵥ (fun i : Index => ξ i) = (fun i : Index => L ξ i) at h
  have hBase : c.transition d (c.chart x) = d.chart x := by
    change d.chart (c.chart.symm (c.chart x)) = d.chart x
    rw [c.chart.left_inv hc]
  have hMatrix : derivativeMatrix L = fixedCotangentTransitionMatrix c d x := by
    change derivativeMatrix (receivingFrequency c d (c.chart x)) =
      (derivativeMatrix (fderiv ℝ (d.transition c) (d.chart x)))ᵀ
    rw [receivingFrequency, derivativeMatrix_adjoint_real, hBase]
  rw [hMatrix] at h
  exact congrArg (WithLp.toLp 2) h.symm

end Burnett.Microlocal.AtlasOverlapKernel
