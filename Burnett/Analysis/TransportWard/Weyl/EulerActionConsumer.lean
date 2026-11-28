import Burnett.Geometry.IntrinsicRicciTrace
import Burnett.Geometry.ManifoldLorentzSignature
import Burnett.Geometry.ManifoldMetricTransition
import Burnett.Geometry.ManifoldVolumeRegularity
import Burnett.Analysis.TransportWard.Weyl.EulerActionIntegral

set_option autoImplicit false
set_option maxHeartbeats 3800000

noncomputable section

namespace Burnett.V03.Palatini

open Filter MeasureTheory Set Burnett.RicciSymbol Burnett.Geometry
open ConnectionDifference CurvatureDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol (Mat)
open scoped BigOperators ContDiff Manifold Topology

open private coordinateJet_eq_of_eventuallyEq from Burnett.Analysis.TransportWard.Weyl.EHCompactVariation
open private coordinateRicci_eq_of_germ from Burnett.Analysis.TransportWard.Weyl.PalatiniVacuumAction

local notation "E" => CoordinateSpace

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M] [T2Space M]

/-- The original ungauged intrinsic vacuum annihilates compact tests of
the existing coordinate Euler density in the true lower metric components. -/
theorem integral_coordinateDensityEuler_eq_zero_of_intrinsicVacuum
    {ι : Type*} [Fintype ι] (S : ι → Mat) (hS : ∀ i, IsSymmetricTensor (S i))
    (B : Field (M := M)) (hB : IsSmooth B) (hSig : HasLorentzSignature B)
    (hVac : IntrinsicRicciTrace.IsVacuum B) (c : M) {K : Set E}
    (hK : IsCompact K) (hKU : K ⊆ (chartAt E c).target) (g h : E → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g (chartAt E c).target) (hh : ContDiffOn ℝ ∞ h (chartAt E c).target)
    (hMatch : EqOn (assembledCoordinateMetric S g) (metricComponents (coordinateBilinear B c))
      (chartAt E c).target)
    (hSupport : ∀ y ∈ (chartAt E c).target \ K, h y = 0) :
    (∫ y in K, ∑ i, h y i * coordinateDensityEuler S g y i) = 0 := by
  let U := (chartAt E c).target
  let G := assembledCoordinateMetric S g
  let G₀ := metricComponents (coordinateBilinear B c)
  have hU : IsOpen U := (chartAt E c).open_target
  have hND (y : E) (hy : y ∈ U) : Matrix.det (assembleMetricComponents S (g y)) ≠ 0 := by
    change Matrix.det (assembledCoordinateMetric S g y) ≠ 0
    rw [hMatch hy]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hSig.isNondegenerate c hy
  have hGerm (y : E) (hy : y ∈ U) : G =ᶠ[𝓝 y] G₀ := by
    filter_upwards [hU.mem_nhds hy] with x hx
    exact hMatch hx
  have hRic (y : E) (hy : y ∈ U) (b d : Index) :
      coordinateRicci (coordinateConnectionFromMetric G) y b d = 0 := by
    have hΓ : coordinateConnectionFromMetric G =ᶠ[𝓝 y] coordinateConnectionFromMetric G₀ := by
      filter_upwards [hU.mem_nhds hy] with x hx
      have hxG := hGerm x hx
      simp only [coordinateConnectionFromMetric, hxG.self_of_nhds, coordinateJet_eq_of_eventuallyEq hxG]
    rw [coordinateRicci_eq_of_germ hΓ]
    exact IntrinsicRicciTrace.coordinateVacuum_of_intrinsic B hB hSig.isSymmetric
      hSig.isNondegenerate hVac c y hy b d
  exact integral_coordinateDensityEuler_eq_zero_of_coordinateVacuum S hS g h hU hK hKU
    hg hh hND hSupport hRic

end Burnett.V03.Palatini
