import Burnett.Analysis.TransportWard.Weyl.PalatiniMetricVariation
import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

/-! First variation of the same ΓΓ density in the Euler field coordinates. -/

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 4600

noncomputable section

namespace Burnett.V03.Palatini

open Set Burnett.RicciSymbol
open Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry.ConnectionDifference
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private hasDerivAt_comp_fieldSegment from Burnett.Analysis.FrozenTransport.V03SegmentTaylor
open private hasDerivAt_affine_scalar from Burnett.Analysis.FrozenTransport.V03EulerJetRemainder
open private coordinateMetricFirstJet_line from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet

local notation "E" => CoordinateSpace

/-- The original lower metric assembled from its finitely many field variables. -/
def assembledCoordinateMetric {ι : Type*} [Fintype ι] (S : ι → Mat) (k : E → ι → ℝ) :
    E → Mat := fun y => assembleMetricComponents S (k y)

theorem coordinateJet_assembledCoordinateMetric {ι : Type*} [Fintype ι] (S : ι → Mat) (k : E → ι → ℝ)
    (x : E) (hk : DifferentiableAt ℝ k x) :
    coordinateJet (assembledCoordinateMetric S k) x = metricJetOfComponents S (coordinateMetricFirstJet k x) := by
  have hd : HasFDerivAt (assembledCoordinateMetric S k)
      ((assembleMetricComponents S).comp (fderiv ℝ k x)) x :=
    (assembleMetricComponents S).hasFDerivAt.comp x hk.hasFDerivAt
  funext a
  rw [metricJetOfComponents_apply]
  funext b c
  have hb := hasFDerivAt_pi'.mp hd b
  have hc := hasFDerivAt_pi'.mp hb c
  change fderiv ℝ (fun y => assembledCoordinateMetric S k y b c) x (EuclideanSpace.single a 1) = _
  rw [hc.fderiv]
  change (assembleMetricComponents S (fderiv ℝ k x (EuclideanSpace.single a 1))) b c = _
  have hbasis : coordinateBasis a = EuclideanSpace.single a 1 := EuclideanSpace.basisFun_apply _ _ a
  simp only [assembleMetricComponents_apply, coordinateMetricFirstJet, hbasis]

/-- The actual weak first variation before spatial integration by parts. -/
def coordinateWeakActionVariation {ι : Type*} [Fintype ι] (S : ι → Mat) (g h : E → ι → ℝ)
    (x : E) : ℝ :=
  let G := assembleMetricComponents S (g x)
  let H := assembleMetricComponents S (h x)
  let p := coordinateMetricFirstJet g x
  let dp := coordinateMetricFirstJet h x
  (1 / 2 : ℝ) * (∑ s, ∑ t, fderiv ℝ (metricActionCoefficient S s t) G H * p s * p t) +
    ∑ s, ∑ t, metricActionCoefficient S s t G * dp s * p t

theorem hasDerivAt_metricActionDensity_assembledAffineVariation {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h : E → ι → ℝ) (x : E)
    (hg : DifferentiableAt ℝ g x) (hh : DifferentiableAt ℝ h x)
    (hn : Matrix.det (assembleMetricComponents S (g x)) ≠ 0) :
    HasDerivAt (fun u =>
      let k := metricAffineVariation (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) u
      metricActionDensity (k x) (coordinateJet k x)) (coordinateWeakActionVariation S g h x) 0 := by
  let G := assembleMetricComponents S (g x)
  let H := assembleMetricComponents S (h x)
  let p := coordinateMetricFirstJet g x
  let dp := coordinateMetricFirstJet h x
  let C (s t : ActionSlot ι) := metricActionCoefficient S s t
  let k (u : ℝ) := metricAffineVariation (assembledCoordinateMetric S g) (assembledCoordinateMetric S h) u
  have hK (u : ℝ) : k u = assembledCoordinateMetric S (fun y => g y + u • h y) := by
    funext y
    simp only [k, metricAffineVariation, assembledCoordinateMetric, map_add, map_smul]
  have hKx (u : ℝ) : k u x = fieldSegment G H u := rfl
  have hJet (u : ℝ) : coordinateJet (k u) x =
      metricJetOfComponents S (fun s => p s + u * dp s) := by
    have hu : DifferentiableAt ℝ (fun y => g y + u • h y) x :=
      (hg.hasFDerivAt.fun_add (hh.hasFDerivAt.fun_const_smul u)).differentiableAt
    rw [hK, coordinateJet_assembledCoordinateMetric S (fun y => g y + u • h y) x hu,
      coordinateMetricFirstJet_line g h x u hg hh]; rfl
  have hFn : (fun u => metricActionDensity (k u x) (coordinateJet (k u) x)) =
      (fun u => (1 / 2 : ℝ) * ∑ s, ∑ t, C s t (fieldSegment G H u) *
        (p s + u * dp s) * (p t + u * dp t)) := by
    funext u
    rw [hKx, hJet, metricActionDensity_eq_coefficient_sum]
  have hC (s t : ActionSlot ι) : HasDerivAt (fun u => C s t (fieldSegment G H u))
      (fderiv ℝ (C s t) G H) 0 := by
    have h0 : fieldSegment G H 0 ∈ nonsingularMetricDomain := by
      change (fieldSegment G H 0).det ≠ 0
      simpa only [fieldSegment, zero_smul, add_zero] using hn
    simpa only [fieldSegment, zero_smul, add_zero] using
      hasDerivAt_comp_fieldSegment (C s t) isOpen_nonsingularMetricDomain
        (contDiffOn_metricActionCoefficient S s t) G H 0 h0
  have hM := HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
    HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) =>
      (((hC s t).mul (hasDerivAt_affine_scalar (p s) (dp s) 0)).mul
        (hasDerivAt_affine_scalar (p t) (dp t) 0))
  have hSwap : (∑ s, ∑ t, C s t G * p s * dp t) = ∑ s, ∑ t, C s t G * dp s * p t := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro t _
    rw [show C t s G = C s t G from congrFun (metricActionCoefficient_swap S t s) G]
    ring
  change HasDerivAt (fun u => metricActionDensity (k u x) (coordinateJet (k u) x)) _ _
  rw [hFn]
  refine (hM.const_mul (1 / 2 : ℝ)).congr_deriv ?_
  change _ = (1 / 2 : ℝ) * (∑ s, ∑ t, fderiv ℝ (C s t) G H * p s * p t) +
    ∑ s, ∑ t, C s t G * dp s * p t
  simp only [Pi.mul_apply, fieldSegment, zero_smul, add_zero, zero_mul, add_mul, Finset.sum_add_distrib, hSwap]
  ring

end Burnett.V03.Palatini
