import Burnett.Geometry.Cotangent.OpenRegion.Cotangent
import Burnett.Geometry.Cotangent.WeightedMomentumTransport

set_option autoImplicit false
set_option maxHeartbeats 4200000

noncomputable section

namespace Burnett.Geometry.OpenRegion

open Set Filter
open TopologicalSpace (Opens)
open scoped ContDiff Manifold Topology
open Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldMetric
open Burnett.Geometry.ManifoldBilinear Burnett.Geometry.UnitNullCompactness
open Burnett.Geometry.CotangentAngularExtension Burnett.Geometry.RadialHamilton
open Burnett.Geometry.UnitNullAngular (Phase chartInverse)
open Burnett.Geometry.ActualTestLift

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

theorem hamiltonVector_openSubtype (U : Opens M) (g : Field (M := M)) (c : U)
    {q : Phase} (hq : q ∈ phaseTarget c) :
    hamiltonVector (chartInverse (restrictBilinear U g) c) q = hamiltonVector (chartInverse g c.val) q := by
  let G := chartInverse (restrictBilinear U g) c
  let H := chartInverse g c.val
  have hG (y : CoordinateSpace) (hy : y ∈ (chartAt CoordinateSpace c).target) : G y = H y := by
    exact congrArg (fun B : LinearMap.BilinForm ℝ CoordinateSpace =>
      InverseField.matrixInverse (FiberMetric.covariant B coordinateBasis))
      (coordinateBilinear_openSubtype U g c hy)
  have hMomentum : (fun ξ : Covector => coordinateP G (q.1, ξ)) =
      (fun ξ : Covector => coordinateP H (q.1, ξ)) := by
    funext ξ
    simp only [coordinateP, hG q.1 hq.1]
  have hBase : (fun y => coordinateP G (y, q.2)) =ᶠ[𝓝 q.1] (fun y => coordinateP H (y, q.2)) := by
    filter_upwards [(chartAt CoordinateSpace c).open_target.mem_nhds hq.1] with y hy
    simp only [coordinateP, hG y hy]
  change hamiltonVector G q = hamiltonVector H q
  apply Prod.ext
  · have hpart : momentumPartial (coordinateP G) q = momentumPartial (coordinateP H) q := by
      funext i
      unfold momentumPartial
      rw [hMomentum]
    exact congrArg (WithLp.toLp 2) hpart
  · funext i
    change -fderiv ℝ (fun y => coordinateP G (y, q.2)) q.1 (coordinateBasis i) =
      -fderiv ℝ (fun y => coordinateP H (y, q.2)) q.1 (coordinateBasis i)
    rw [hBase.fderiv_eq]

/-- The actual Hamiltonian derivation commutes with the open-submanifold
restriction of both the metric and the scalar test. -/
theorem actualHamiltonDerivative_openSubtype (U : Opens M) (g : Field (M := M))
    (a : CotangentBundle M → ℝ) (p : CotangentBundle U) :
    actualHamiltonDerivative (restrictBilinear U g) (a ∘ cotangentOpenVal U) p =
      actualHamiltonDerivative g a (cotangentOpenVal U p) := by
  let c := p.1
  have hp : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  let q := cotangentChart c p
  have hq : q ∈ phaseTarget c := cotangentChart_mapsTo c hp
  have hEq : (a ∘ cotangentOpenVal U) ∘ cotangentChartInverse c =ᶠ[𝓝 q]
      a ∘ cotangentChartInverse c.val := by
    filter_upwards [(isOpen_phaseTarget c).mem_nhds hq] with z hz
    change a (cotangentOpenVal U (cotangentChartInverse c z)) = a (cotangentChartInverse c.val z)
    rw [cotangentChartInverse_openVal U c hz]
  change fderiv ℝ ((a ∘ cotangentOpenVal U) ∘ cotangentChartInverse c) q
      (hamiltonVector (chartInverse (restrictBilinear U g) c) q) =
    fderiv ℝ (a ∘ cotangentChartInverse c.val) (cotangentChart c.val (cotangentOpenVal U p))
      (hamiltonVector (chartInverse g c.val) (cotangentChart c.val (cotangentOpenVal U p)))
  rw [cotangentChart_openVal U c hp, hEq.fderiv_eq, hamiltonVector_openSubtype U g c hq]

theorem dualEnergy_openSubtype (U : Opens M) (g : Field (M := M))
    (hn : IsNondegenerate g) (hs : IsSymmetric g) (p : CotangentBundle U) :
    dualEnergy (restrictBilinear U g) (fun x => hn x.val) p = dualEnergy g hn (cotangentOpenVal U p) := by
  let c := p.1
  have hp : p ∈ cotangentSource c := mem_chart_source CoordinateSpace c
  have hpM : cotangentOpenVal U p ∈ cotangentSource c.val := hp.2
  rw [dualEnergy_chart (restrictBilinear U g) (fun x => hn x.val) (fun x => hs x.val) c p hp,
    dualEnergy_chart g hn hs c.val (cotangentOpenVal U p) hpM]
  have hChart := cotangentChart_openVal U c hp
  have hy := (cotangentChart_mapsTo c hp).1
  change (chartAt CoordinateSpace c p.1) ∈ (chartAt CoordinateSpace c).target at hy
  have hB := coordinateBilinear_openSubtype U g c hy
  have hyEq : chartAt CoordinateSpace c.val (cotangentOpenVal U p).1 = chartAt CoordinateSpace c p.1 :=
    congrArg Prod.fst hChart
  rw [hyEq]
  exact congrArg₂ symbolNorm
    (congrArg (fun B : LinearMap.BilinForm ℝ CoordinateSpace =>
      InverseField.matrixInverse (FiberMetric.covariant B coordinateBasis)) hB)
    (congrArg Prod.snd hChart).symm

end Burnett.Geometry.OpenRegion
