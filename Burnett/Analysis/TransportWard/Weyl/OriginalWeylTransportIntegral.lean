import Burnett.Analysis.Microlocal.Overlap.AtlasAngularPhaseEncoding
import Burnett.Analysis.Microlocal.Overlap.NormalizedAmplitudePlateauRestriction
import Burnett.Analysis.TransportClosure.C04HamiltonChartRegularity
import Burnett.Analysis.TransportClosure.HamiltonCompactBaseIntegrability

set_option autoImplicit false
set_option maxHeartbeats 5000000

noncomputable section

namespace Burnett.C04

open Set Filter MeasureTheory Burnett.RicciSymbol
open scoped ContDiff Manifold Topology
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear ManifoldMetricTransition
open UnitNullCompactness CotangentAngularExtension
open Burnett.Geometry.MaximalChart (AtlasChart)
open Burnett.Geometry.UnitNullAngular (chartInverse)
open Burnett.Geometry.UnitCosphere (Cosphere projection coe_mem_punctured continuous_projection)
open Burnett.Microlocal.Overlap (atlasChartUnitCovector amplitudeCosphereWindow)
open Burnett.Bianchi.RayIdentification (canonicalBracket coordinateHamiltonian)
open Burnett.RotatingNullMoments.CanonicalHamilton (basePartial momentumPartial)

local notation "E" => CoordinateSpace

private theorem canonicalBracket_congr_of_coordinate_germs
    {P Q a b : E → Covector → ℝ} (x : E) (ξ : Covector)
    (hP : (fun y => P y ξ) =ᶠ[𝓝 x] fun y => Q y ξ)
    (ha : (fun y => a y ξ) =ᶠ[𝓝 x] fun y => b y ξ)
    (hQ : P x =ᶠ[𝓝 ξ] Q x) (hb : a x =ᶠ[𝓝 ξ] b x) :
    canonicalBracket P a x ξ = canonicalBracket Q b x ξ := by
  simp only [canonicalBracket, basePartial, momentumPartial, hP.fderiv_eq, ha.fderiv_eq,
    hQ.fderiv_eq, hb.fderiv_eq]

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [T2Space M]

/-- The V03 preferred-chart Weyl limit uses the same Hamilton integrand and
same physical cosphere measure as C04. The compact base window may be
enlarged to the whole chart because the Hamilton derivative vanishes off it. -/
theorem originalWeylTransportIntegral_eq_chart (r : Metric (M := M)) (B : Field (M := M))
    (hn : IsNondegenerate B) (hs : IsSymmetric B) (c : M) (μ : Measure (Cosphere r))
    (b : CotangentBundle M → ℝ) (a : E → Covector → ℝ) (K : Set M)
    (hK : IsCompact K) (hSub : K ⊆ (chartAt E c).source)
    (hZero : ∀ p ∈ puncturedCotangent, p.proj ∉ K → b p = 0)
    (ha : ∀ x ∈ (chartAt E c).target, ∀ ξ ≠ 0, a x ξ = b (cotangentChartInverse c (x, ξ))) :
    ∫ p in amplitudeCosphereWindow r K,
      canonicalBracket (coordinateHamiltonian (metricComponents (coordinateBilinear B c))) a
        ((AtlasChart.atPoint c).chart (projection p)) (atlasChartUnitCovector (AtlasChart.atPoint c) p) ∂μ =
    ∫ p in {p : Cosphere r | p.val.proj ∈ (chartAt E c).source}, chartHamiltonDerivative c B hn b p.val ∂μ := by
  let e := chartAt E c
  let W := amplitudeCosphereWindow r K
  let V := {p : Cosphere r | p.val.proj ∈ e.source}
  let P := coordinateHamiltonian (metricComponents (coordinateBilinear B c))
  let Q := chartHamiltonian c B hn
  let b' (x : E) (ξ : Covector) : ℝ := b (cotangentChartInverse c (x, ξ))
  have hW : MeasurableSet W := (hK.isClosed.preimage (continuous_projection r)).measurableSet
  have hV : MeasurableSet V := (e.open_source.preimage (continuous_projection r)).measurableSet
  have hWV : W ⊆ V := fun _ h => hSub h
  have hPQ (x : E) (hx : x ∈ e.target) (ξ : Covector) : P x ξ = Q x ξ :=
    (chartHamiltonian_eq_inverseMetric c B hn hs (x, ξ) ⟨hx, trivial⟩).symm
  calc
    _ = ∫ p in W, chartHamiltonDerivative c B hn b p.val ∂μ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem (μ := μ) hW] with p hp
      have hc : p.val.proj ∈ e.source := hWV hp
      let x := e (projection p)
      let ξ := cotangentCoords c p.val
      have hx : x ∈ e.target := e.mapsTo hc
      have hξ : ξ ≠ 0 := cotangentCoords_ne_zero_of_punctured c p.val hc (coe_mem_punctured r p)
      have hPref : atlasChartUnitCovector (AtlasChart.atPoint c) p = ξ := by
        unfold atlasChartUnitCovector
        rw [FixedCotangentChart.fixedChartPhase_preferred c p.val hc]
      change canonicalBracket P a x (atlasChartUnitCovector (AtlasChart.atPoint c) p) =
        canonicalBracket Q b' x ξ
      rw [hPref]
      have hNear : ∀ᶠ y in 𝓝 x, y ∈ e.target := e.open_target.mem_nhds hx
      have hNearξ : ∀ᶠ η in 𝓝 ξ, η ≠ 0 := isOpen_compl_singleton.mem_nhds hξ
      exact canonicalBracket_congr_of_coordinate_germs x ξ
        (hNear.mono (fun y hy => hPQ y hy ξ)) (hNear.mono (fun y hy => ha y hy ξ hξ))
        (Eventually.of_forall (hPQ x hx)) (hNearξ.mono (fun η hη => ha x hx η hη))
    _ = ∫ p in V, chartHamiltonDerivative c B hn b p.val ∂μ := by
      symm
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero hV hWV
      intro p hp
      exact chartHamiltonDerivative_eq_zero_of_outside_base c B hn b hK.isClosed hZero p.val
        (coe_mem_punctured r p) hp.1 hp.2

end Burnett.C04
