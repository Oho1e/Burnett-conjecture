import Burnett.Analysis.TransportWard.Weyl.PalatiniRicci
import Burnett.Analysis.TransportWard.Weyl.PalatiniBoundaryDivergence

/-! Signed Einstein–Hilbert density variation and its exact vacuum specialization. -/

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option maxRecDepth 4300

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.V02.EinsteinHilbert
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.CurvatureDifference
open scoped ContDiff Topology

local notation "E" => CoordinateSpace

/-- The signed first variation of the actual coordinate Einstein–Hilbert density.
The direction is a lower metric variation. The bulk term contains the
trace-reversed Ricci tensor with both indices raised. -/
theorem hasDerivAt_einsteinHilbertDensity_metricAffineVariation (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hgs : ∀ y ∈ U, IsSymmetricTensor (g y)) (hhs : ∀ y ∈ U, IsSymmetricTensor (h y))
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (x : E) (hx : x ∈ U) :
    HasDerivAt (fun t => einsteinHilbertDensity (metricAffineVariation g h t) x)
      (metricDensity (g x) * physicalPairing (inverseMatrix (g x))
          (coordinateRicci (coordinateConnectionFromMetric g) x) (h x) -
        coordinateDivergence (palatiniBoundaryVector g (coordinateConnectionVariation g h)) x) 0 := by
  let C := coordinateConnectionVariation g h
  let Q := covariantDivergenceDifference (coordinateConnectionFromMetric g x) (C x)
    (coordinateConnectionJet C x)
  have hC : DifferentiableConnectionAt C x := fun a b c =>
    ((contDiffOn_coordinateConnectionVariation g h hU hg hh hn a b c).contDiffAt
      (hU.mem_nhds hx)).differentiableAt (by simp)
  have hD := hasDerivAt_einsteinHilbertDensity_of_RicciVariation g h x (hn x hx) Q
    (hasDerivAt_coordinateRicci_metricAffineVariation g h hU hg hh hgs hhs hn x hx)
  rw [neg_metricTrace_inverseMetricDensityVariation_eq_physicalPairing g h x (hgs x hx),
    ← coordinateDivergence_palatiniBoundaryVector g C hU hg hn hgs x hx hC] at hD
  exact hD

/-- The true first variation at a Ricci-flat point is the negative ordinary
divergence of the actual Palatini vector density. -/
theorem hasDerivAt_einsteinHilbertDensity_of_coordinateVacuum (g h : E → Mat) {U : Set E}
    (hU : IsOpen U) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun y => g y i j) U)
    (hh : ∀ i j, ContDiffOn ℝ ∞ (fun y => h y i j) U)
    (hgs : ∀ y ∈ U, IsSymmetricTensor (g y)) (hhs : ∀ y ∈ U, IsSymmetricTensor (h y))
    (hn : ∀ y ∈ U, Matrix.det (g y) ≠ 0) (x : E) (hx : x ∈ U)
    (hVac : ∀ b c, coordinateRicci (coordinateConnectionFromMetric g) x b c = 0) :
    HasDerivAt (fun t => einsteinHilbertDensity (metricAffineVariation g h t) x)
      (-coordinateDivergence (palatiniBoundaryVector g (coordinateConnectionVariation g h)) x) 0 := by
  have hRic : coordinateRicci (coordinateConnectionFromMetric g) x = 0 :=
    funext fun b => funext fun c => hVac b c
  have hD := hasDerivAt_einsteinHilbertDensity_metricAffineVariation g h hU hg hh hgs hhs hn x hx
  simpa [hRic, physicalPairing, metricTrace, tensorPairing] using hD

end Burnett.V03.Palatini
