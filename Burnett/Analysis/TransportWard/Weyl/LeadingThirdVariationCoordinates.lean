import Burnett.Analysis.TransportWard.Weyl.PrincipalVariationDensityBridge
import Burnett.Analysis.TransportWard.Weyl.EulerActionVariation
import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
import Burnett.Analysis.FrozenTransport.V03SegmentTaylor

set_option autoImplicit false
set_option maxHeartbeats 2900000

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol Burnett.A02.FrequencySplit Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators ContDiff Matrix.Norms.Elementwise

open private metricKineticBilinear from Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient
open private hasDerivAt_comp_fieldSegment from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

private theorem principalLeg_component_sum {J : Type*} [Fintype J]
    (S : J → Mat) (G H : Mat) (hG : G ∈ nonsingularMetricDomain) (p q : ActionSlot J → ℝ) :
    principalLeg G H (metricJetOfComponents S p) (metricJetOfComponents S q) =
      ∑ s : ActionSlot J, ∑ t : ActionSlot J, fderiv ℝ (metricActionCoefficient S s t) G H * p s * q t := by
  let X := metricJetOfComponents S p
  let Y := metricJetOfComponents S q
  have hEq (g : Mat) : metricKineticCoefficient g X Y =
      ∑ s : ActionSlot J, ∑ t : ActionSlot J, metricActionCoefficient S s t g * p s * q t := by
    change metricKineticBilinear g X Y = _
    simp only [X, Y, metricJetOfComponents, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    change q s * (p t * metricActionCoefficient S t s g) = _
    ring
  have h0 : fieldSegment G H 0 ∈ nonsingularMetricDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using hG
  have hD (s t : ActionSlot J) : HasDerivAt (fun u => metricActionCoefficient S s t
      (fieldSegment G H u) * p s * q t) (fderiv ℝ (metricActionCoefficient S s t) G H * p s * q t) 0 := by
    simpa only [fieldSegment, zero_smul, add_zero] using
      (((hasDerivAt_comp_fieldSegment (metricActionCoefficient S s t) isOpen_nonsingularMetricDomain
        (contDiffOn_metricActionCoefficient S s t) G H 0 h0).mul_const (p s)).mul_const (q t))
  have hDsum := HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
    HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => hD s t
  have hLeg := hasDerivAt_metricKineticCoefficient_path G H hG X Y
  have hPath : (fun u : ℝ => metricKineticCoefficient (G + u • H) X Y) =
      fun u => ∑ s, ∑ t, metricActionCoefficient S s t (fieldSegment G H u) * p s * q t := by
    funext u
    exact hEq (fieldSegment G H u)
  rw [hPath] at hLeg
  exact hLeg.unique hDsum

/-- The A03 principal density depends on the original assembled tensors
and their first coordinate jets, independently of the fixed real field basis. -/
theorem principalVariationDensity_re_eq_actualTensorJets {J : Type} [Fintype J]
    (S : J → Mat) (g : E → J → ℝ) (z w : RealEnergyField J) (x : E)
    (hG : assembleMetricComponents S (g x) ∈ nonsingularMetricDomain) :
    let G := assembleMetricComponents S (g x)
    let h (y : E) (i : J) := (z.val i y).re
    let v (y : E) (i : J) := (w.val i y).re
    let H := assembleMetricComponents S (h x)
    let K := assembleMetricComponents S (v x)
    let dh := coordinateJet (assembledCoordinateMetric S h) x
    let dv := coordinateJet (assembledCoordinateMetric S v) x
    (principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x).re =
      principalLeg G K dh dh + 2 * principalLeg G H dv dh := by
  intro G h v H K dh dv
  have hs : ContDiff ℝ ∞ h := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (z.val i).smooth'
  have hv : ContDiff ℝ ∞ v := contDiff_pi.mpr fun i => Complex.reCLM.contDiff.comp (w.val i).smooth'
  have hJ : dh = metricJetOfComponents S (coordinateMetricFirstJet h x) :=
    coordinateJet_assembledCoordinateMetric S h x (hs.differentiable (by simp) x)
  have hK : dv = metricJetOfComponents S (coordinateMetricFirstJet v x) :=
    coordinateJet_assembledCoordinateMetric S v x (hv.differentiable (by simp) x)
  rw [principalVariationDensity_eq_actualLeadingThirdVariation, Complex.ofReal_re, hJ, hK,
    principalLeg_component_sum S G K hG, principalLeg_component_sum S G H hG]
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem principalVariationDensity_re_eq_of_assembledFields
    {J K : Type} [Fintype J] [Fintype K]
    (S : J → Mat) (T : K → Mat) (g : E → J → ℝ) (b : E → K → ℝ)
    (z w : RealEnergyField J) (z' w' : RealEnergyField K) (x : E)
    (hG : assembleMetricComponents S (g x) ∈ nonsingularMetricDomain)
    (hB : assembleMetricComponents S (g x) = assembleMetricComponents T (b x))
    (hZ : assembledCoordinateMetric S (fun y i => (z.val i y).re) =
      assembledCoordinateMetric T (fun y i => (z'.val i y).re))
    (hW : assembledCoordinateMetric S (fun y i => (w.val i y).re) =
      assembledCoordinateMetric T (fun y i => (w'.val i y).re)) :
    (principalVariationDensity (eulerPrincipalVariationCoefficient S g) z.val (fun i => w.val i) x).re =
      (principalVariationDensity (eulerPrincipalVariationCoefficient T b) z'.val (fun i => w'.val i) x).re := by
  have hG' : assembleMetricComponents T (b x) ∈ nonsingularMetricDomain := hB ▸ hG
  have hz : assembleMetricComponents S (fun i => (z.val i x).re) =
      assembleMetricComponents T (fun i => (z'.val i x).re) := congrFun hZ x
  have hw : assembleMetricComponents S (fun i => (w.val i x).re) =
      assembleMetricComponents T (fun i => (w'.val i x).re) := congrFun hW x
  rw [principalVariationDensity_re_eq_actualTensorJets S g z w x hG,
    principalVariationDensity_re_eq_actualTensorJets T b z' w' x hG', hB, hZ, hW, hz, hw]

end Burnett.V03.Palatini
