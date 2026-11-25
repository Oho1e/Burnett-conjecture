import Burnett.Analysis.FrozenTransport.CompactReceivingCubicCoefficients
import Burnett.Analysis.FrozenTransport.FrozenDensityCubicVertex

set_option autoImplicit false
set_option maxRecDepth 5400
set_option maxHeartbeats 7600000
noncomputable section

namespace Burnett.C02

open Burnett.A02.FrequencySplit (EnergyIndex)
open Burnett.Analysis.TransportWardSymbol Burnett.RicciSymbol Burnett.V03 Burnett.V04
open Burnett.Microlocal.PhysicalDensity (OrderedPair)
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

open private orderedTensorBasis coordinateDerivativeBasis from Burnett.Analysis.FrozenTransport.CompactReceivingCubicCoefficients

/-- The ordered matrix basis identifies the same real coordinates throughout
the frozen energy and the V03/V04 coefficient and vertex. -/
def frozenActionOrderedBasis (k : OrderedPair) : Mat :=
  orderedTensorBasis k

private theorem frozenActionAxisJet_eq_plane (a : Index) (k : OrderedPair) :
    metricAxisJet frozenActionOrderedBasis (a,k) =
      planeJet (coordinateDerivativeBasis a) (orderedTensorBasis k) := by
  classical
  funext d b c
  by_cases h : d = a
  · subst d
    simp [metricAxisJet, planeJet, coordinateDerivativeBasis, frozenActionOrderedBasis]
  · simp [metricAxisJet, planeJet, coordinateDerivativeBasis, h]

theorem frozenActionCubicLinear_eq_metricActionCoefficient_fderiv (G : Mat)
    (hG : G ∈ nonsingularMetricDomain) (a d : Index) (i j k : OrderedPair) :
    frozenActionCubicLinear G ((a,d),(i,j)) k =
      fderiv ℝ (metricActionCoefficient frozenActionOrderedBasis (a,i) (d,j)) G (frozenActionOrderedBasis k) := by
  let f := metricActionCoefficient frozenActionOrderedBasis (a,i) (d,j)
  let H := frozenActionOrderedBasis k
  have hC := (contDiffOn_metricActionCoefficient frozenActionOrderedBasis (a,i) (d,j)).contDiffAt
    (isOpen_nonsingularMetricDomain.mem_nhds hG)
  have hC₁ : ContDiffAt ℝ 1 f G := by simpa only [Nat.cast_one] using contDiffAt_infty.mp hC 1
  have hPath : HasDerivAt (fun t : ℝ => G + t • H) H 0 := by
    simpa only [one_smul, zero_add] using (((hasDerivAt_id (0 : ℝ)).smul_const H).const_add G)
  have hMetric : HasFDerivAt f (fderiv ℝ f G) (G + (0 : ℝ) • H) := by
    simpa only [zero_smul, add_zero] using (hC₁.differentiableAt le_rfl).hasFDerivAt
  have hDer := (hMetric.comp_hasDerivAt 0 hPath).deriv
  have hCubic := frozenActionCubicLinear_derivative G hG ((a,d),(i,j)) k
  have hEq (t : ℝ) : f (G + t • H) = metricKineticCoefficient (G + t • orderedTensorBasis k)
      (planeJet (coordinateDerivativeBasis a) (orderedTensorBasis i))
      (planeJet (coordinateDerivativeBasis d) (orderedTensorBasis j)) := by
    unfold f metricActionCoefficient
    rw [frozenActionAxisJet_eq_plane, frozenActionAxisJet_eq_plane]
    rfl
  rw [← funext hEq] at hCubic
  exact hCubic.trans hDer

/-- The complex linear coefficient used in the V04 vertex is the same
component array as the real A02 coefficient of the second derivative. -/
theorem frozenDensityCubicDirection_eq_frozenActionCubicLinear (G : Mat)
    (hG : G ∈ nonsingularMetricDomain) (a d : Index) (i j : OrderedPair) (H : OrderedPair → ℂ) :
    densityCoefficientDirection frozenActionOrderedBasis G (a,i) (d,j) H =
      ∑ k, (frozenActionCubicLinear G ((a,d),(i,j)) k : ℂ) * H k := by
  unfold densityCoefficientDirection
  simp only [frozenActionCubicLinear_eq_metricActionCoefficient_fderiv G hG]

end Burnett.C02
