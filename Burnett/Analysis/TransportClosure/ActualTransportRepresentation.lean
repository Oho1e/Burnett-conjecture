import Burnett.Analysis.TransportClosure.OriginalTransportFromLocalBounds
import Burnett.Analysis.TransportClosure.CanonicalHamiltonBracketAgreement

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.C04

open MeasureTheory Set
open scoped ContDiff Manifold Topology
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension
open Burnett.Geometry.UnitCosphere (Cosphere coe_mem_punctured)
open Burnett.Geometry.ActualTestLift (actualHamiltonDerivative)

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem actualHamiltonDerivative_eq_basePointHamiltonDerivative
    (r : Metric (M := M)) (g : Field (M := M)) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent) (p : Cosphere r) :
    actualHamiltonDerivative g a p.val = basePointHamiltonDerivative g hn a p.val := by
  exact Burnett.Geometry.ActualTestLift.chartHamiltonDerivative_eq_actual_canonicalBracket g hn hs p.val.1 a ha
    (mem_chart_source CoordinateSpace p.val.1) (coe_mem_punctured r p)

/-- The transport law read in the canonical chart is the actual Hamilton
derivative consumed by the lift and open-region restriction. Both laws use
the original unit-cosphere measure directly. -/
theorem transport_actualHamilton_of_basePointHamiltonTransport
    (r : Metric (M := M)) (g : Field (M := M)) (hn : IsNondegenerate g) (hs : IsSymmetric g)
    (μ : Measure (Cosphere r))
    (ht : ∀ a : CotangentBundle M → ℝ, IsDegreeOneTransportTest a →
      Integrable (fun p : Cosphere r => basePointHamiltonDerivative g hn a p.val) μ ∧
      (∫ p : Cosphere r, basePointHamiltonDerivative g hn a p.val ∂μ) = 0)
    (a : CotangentBundle M → ℝ)
    (ha : ContMDiffOn CotangentModelWithCorners 𝓘(ℝ) ∞ a puncturedCotangent)
    (hhom : ∀ p ∈ puncturedCotangent, ∀ t > (0 : ℝ), a (cotangentScale t p) = t * a p)
    (hSupp : ∃ K : Set M, IsCompact K ∧ tsupport a ⊆ (fun p => p.1) ⁻¹' K) :
    Integrable (fun p : Cosphere r => actualHamiltonDerivative g a p.val) μ ∧
      (∫ p : Cosphere r, actualHamiltonDerivative g a p.val ∂μ) = 0 := by
  obtain ⟨K, hK, hB⟩ := hSupp
  have hb : IsDegreeOneTransportTest a := ⟨ha, hhom, K, hK, fun p _ hp =>
    image_eq_zero_of_notMem_tsupport (fun h => hp (hB h))⟩
  simp_rw [actualHamiltonDerivative_eq_basePointHamiltonDerivative r g hn hs a ha]
  exact ht a hb

end Burnett.C04
