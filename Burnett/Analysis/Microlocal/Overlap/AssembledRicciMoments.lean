import Burnett.Analysis.ChartTensorRicciTests
import Burnett.Analysis.ScalarCurvatureFromMoments
import Burnett.Analysis.Microlocal.PhysicalChartCover
import Burnett.Geometry.Cotangent.CompactTestIntegrals

/-! The actual Ricci moments for arbitrary compactly supported tensor tests. -/

set_option autoImplicit false
set_option maxHeartbeats 760000
noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.RicciSymbol
open Burnett.Geometry ConnectionDifference ManifoldBilinear ManifoldMetric ManifoldMetricTransition
open BackgroundConnection CurvatureDifference ContravariantTensor UnitNullCompactness
open Burnett.Analysis.ChartTensorRicciTests
open Burnett.Analysis.ScalarCurvatureFromMoments (HasRicciMoments)
open Burnett.Geometry.CotangentTests (integral_eq_of_compact_base_local_tests)
open Burnett.Microlocal.CountableAuxiliaryCharts (CompactChartInput)
open Burnett.X02.SobolevTestJet (D Space)
open scoped BigOperators ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
variable [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
variable [MeasurableSpace (CotangentBundle M)] [BorelSpace (CotangentBundle M)]

/-- On one measure, the component moments in the represented nonzero windows
of a cover give the global moment of every genuine compact tensor test. -/
theorem hasRicciMoments_of_nonzero_chartMoments
    {ι : Type*} (B : Field (M := M)) (hB : IsSmooth B) (hs : IsSymmetric B) (hn : IsNondegenerate B)
    (q : ι → CompactChartInput M) (hCover : ⋃ i, (q i).nonzeroLocus = univ)
    (μ : Measure (CotangentBundle M))
    (hMom : ∀ a (ψ : D), tsupport (ψ : Space → ℝ) ⊆ {y | ((q a).cutoff : Space → ℝ) y ≠ 0} →
      ∀ i j : Index,
        let c := (q a).center
        let R (y : Space) := (ψ : Space → ℝ) y *
          coordinateRicci (computedConnection (coordinateBilinear B c)) y i j
        let P (p : CotangentBundle M) := (ψ : Space → ℝ) (chartAt CoordinateSpace c p.proj) *
          (cotangentCoords c p i * cotangentCoords c p j)
        let V := ManifoldVolume.coordinateMeasure B c
        let S := (fun p : CotangentBundle M => p.proj) ⁻¹' (q a).nonzeroLocus
        Integrable R V ∧ IntegrableOn P S μ ∧ (∫ y, R y ∂V) = ∫ p in S, P p ∂μ) :
    HasRicciMoments B μ := by
  intro Q hQ
  let π := fun p : CotangentBundle M => p.proj
  let U (i : ι) := (q i).nonzeroLocus
  let K : Set M := closure {x | Q x ≠ 0}
  let R := intrinsicTensorBase B Q
  let P := intrinsicTensorPhase Q
  have hK : IsCompact K := hQ.2.1
  have hKcover : K ⊆ ⋃ i, U i := by
    change K ⊆ ⋃ i, (q i).nonzeroLocus
    rw [hCover]
    exact subset_univ _
  have hZero (x : M) (hx : x ∉ K) : Q x = 0 := by
    by_contra hnz
    exact hx (subset_closure hnz)
  have hRzero : ∀ᵐ x ∂ManifoldVolume.geometricMeasure B, x ∉ K → R x = 0 :=
    Eventually.of_forall (fun x hx => by
      have hxChart := mem_chart_source CoordinateSpace x
      change intrinsicTensorBase B Q x = 0
      rw [intrinsicTensorBase_eq_components B hB hs hn Q x x hxChart]
      simp only [contravariantComponents_chart Q x x hxChart, hZero x hx,
        LinearMap.zero_apply, zero_mul, Finset.sum_const_zero])
  have hPzero : ∀ᵐ p ∂μ, π p ∉ K → P p = 0 := Eventually.of_forall (fun p hp => by
    simp only [P, intrinsicTensorPhase, hZero p.proj hp, LinearMap.zero_apply])
  apply integral_eq_of_compact_base_local_tests π (ManifoldVolume.geometricMeasure B) μ U
    (fun i => (q i).isOpen_nonzeroLocus) hK hKcover R P hRzero hPzero
  intro a φ hφ hc hφU
  let c := (q a).center
  have hSrc : U a ⊆ (chartAt CoordinateSpace c).source := fun _ hx => hx.1
  refine local_intrinsicTensor_moment_of_coordinateMoments B hB hs hn c (U a) (q a).isOpen_nonzeroLocus
    hSrc μ ?_ Q hQ.2.2 φ hφ hc hφU
  intro ψ hψ i j
  exact hMom a ψ (hψ.trans (by
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2)) i j

end Burnett.Microlocal.Overlap
