import Burnett.Analysis.TransportWard.Weyl.LinearizedEulerSymmetry
import Burnett.Analysis.TransportWard.Weyl.OriginalEulerPath

/-! The actual affine Euler derivative has the frozen `-C` coefficient on
the second spatial jet of the variation. -/

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option maxRecDepth 4400

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set Burnett.RicciSymbol Burnett.Analysis.TransportWardSymbol
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldMetricTransition ManifoldBilinear
open scoped BigOperators ContDiff Manifold Matrix.Norms.Elementwise Topology

open private coordinateMetricFirstJet_line coordinateMetricSecondJet_line from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private hasDerivAt_comp_fieldSegment hasDerivAt_fieldSegment from Burnett.Analysis.FrozenTransport.V03SegmentTaylor
open private hasDerivAt_affine_scalar from Burnett.Analysis.FrozenTransport.V03EulerJetRemainder

local notation "E" => CoordinateSpace
local notation "I" => SymmetricMetricSlot

/-- This part of the affine Euler derivative holds the background second
spatial jet fixed. The variation enters only through its zeroth and first jets. -/
def metricEulerJetLowerLinearization {ι : Type*} [Fintype ι] (S : ι → Mat) (G H : Mat)
    (p dp : ActionSlot ι → ℝ) (q : Fin 4 → ActionSlot ι → ℝ) (i : ι) : ℝ :=
  deriv (fun t => metricEulerAtJet S (fieldSegment G H t) (fieldSegment p dp t) q i) 0

/-- The actual full `E'` from the affine ΓΓ Hessian split by derivative
order on the perturbation. The background second jet stays in the lower part. -/
theorem linearizedCoordinateDensityEuler_eq_lower_sub_secondJet {ι : Type*} [Fintype ι]
    (S : ι → Mat) (g h : E → ι → ℝ) {U : Set E} (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (x : E) (hx : x ∈ U) (hn : (assembleMetricComponents S (g x)).det ≠ 0)
    (i : ι) :
    linearizedCoordinateDensityEuler S g h x i =
      metricEulerJetLowerLinearization S (assembleMetricComponents S (g x))
        (assembleMetricComponents S (h x)) (coordinateMetricFirstJet g x)
        (coordinateMetricFirstJet h x) (coordinateMetricSecondJet g x) i -
      ∑ a, ∑ s, metricActionCoefficient S (a, i) s (assembleMetricComponents S (g x)) *
        coordinateMetricSecondJet h x a s := by
  let G := assembleMetricComponents S (g x)
  let H := assembleMetricComponents S (h x)
  let p := coordinateMetricFirstJet g x
  let dp := coordinateMetricFirstJet h x
  let q := coordinateMetricSecondJet g x
  let dq := coordinateMetricSecondJet h x
  let lo (t : ℝ) := metricEulerAtJet S (fieldSegment G H t) (fieldSegment p dp t) q i
  let top (t : ℝ) := ∑ a, ∑ s, metricActionCoefficient S (a, i) s (fieldSegment G H t) * dq a s
  have h0 : fieldSegment G H 0 ∈ nonsingularMetricDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using (show G ∈ nonsingularMetricDomain from hn)
  have hSeg : ∀ᶠ t : ℝ in 𝓝 0, fieldSegment G H t ∈ nonsingularMetricDomain :=
    (hasDerivAt_fieldSegment G H 0).continuousAt.eventually
      (isOpen_nonsingularMetricDomain.mem_nhds h0)
  have hC (a : Fin 4) (s : ActionSlot ι) :
      DifferentiableAt ℝ (fun t => metricActionCoefficient S (a, i) s (fieldSegment G H t)) 0 :=
    (hasDerivAt_comp_fieldSegment _ isOpen_nonsingularMetricDomain
      (contDiffOn_metricActionCoefficient S (a, i) s) G H 0 h0).differentiableAt
  have hD (s r : ActionSlot ι) :
      DifferentiableAt ℝ (fun t => metricEulerLowerCoefficient S i s r (fieldSegment G H t)) 0 :=
    (hasDerivAt_comp_fieldSegment _ isOpen_nonsingularMetricDomain
      (contDiffOn_metricEulerLowerCoefficient S i s r) G H 0 h0).differentiableAt
  have hp (s : ActionSlot ι) : DifferentiableAt ℝ (fun t => fieldSegment p dp t s) 0 :=
    (hasDerivAt_affine_scalar (p s) (dp s) 0).differentiableAt
  have hlo : DifferentiableAt ℝ lo 0 :=
    (DifferentiableAt.fun_sum fun s _ => DifferentiableAt.fun_sum fun r _ =>
      ((hD s r).mul (hp s)).mul (hp r)).sub
      (DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun s _ =>
        (hC a s).mul_const (q a s))
  have htop : DifferentiableAt ℝ top 0 :=
    DifferentiableAt.fun_sum fun a _ => DifferentiableAt.fun_sum fun s _ =>
      (hC a s).mul_const (dq a s)
  have hEq : (fun t : ℝ => coordinateDensityEuler S (fun y => g y + t • h y) x i) =ᶠ[𝓝 0]
      (fun t => lo t - t * top t) := by
    filter_upwards [hSeg] with t ht
    have hG : assembleMetricComponents S (g x + t • h x) = fieldSegment G H t := by
      simp only [G, H, fieldSegment, map_add, map_smul]
    have hnd : (assembleMetricComponents S (g x + t • h x)).det ≠ 0 := by
      rw [hG]
      exact ht
    have hgx := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hhx := (hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    rw [coordinateDensityEuler_eq_metricEulerAtJet S hU _ (hg.add (hh.const_smul t)) x hx hnd,
      hG, coordinateMetricFirstJet_line g h x t hgx hhx,
      coordinateMetricSecondJet_line hU g h hg hh x hx t]
    have hLin : (∑ a, ∑ s, metricActionCoefficient S (a, i) s (fieldSegment G H t) *
        fieldSegment q dq t a s) =
        (∑ a, ∑ s, metricActionCoefficient S (a, i) s (fieldSegment G H t) * q a s) +
          t * top t := by
      simp only [fieldSegment, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
        top, Finset.mul_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro s _
      ring
    change metricEulerAtJet S (fieldSegment G H t) (fieldSegment p dp t) (fieldSegment q dq t) i =
      lo t - t * top t
    simp only [lo, metricEulerAtJet, hLin]
    ring
  have hdTop : HasDerivAt (fun t : ℝ => t * top t) (top 0) 0 := by
    simpa only [id_eq, one_mul, zero_mul, add_zero, zero_add] using
      (hasDerivAt_id (0 : ℝ)).mul htop.hasDerivAt
  change deriv (fun t : ℝ => coordinateDensityEuler S (fun y => g y + t • h y) x i) 0 =
    deriv lo 0 - ∑ a, ∑ s, metricActionCoefficient S (a, i) s G * dq a s
  simpa only [top, fieldSegment, zero_smul, add_zero] using
    ((hlo.hasDerivAt.sub hdTop).congr_of_eventuallyEq hEq).deriv

variable {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold Model ∞ M]

/-- This is the first derivative of the very same path used for tested
vacuum on the original fields. Its background may be nonvacuum. -/
theorem deriv_originalChartEulerPath_eq_lower_sub_secondJet
    (B B' : Field (M := M)) (hB : IsSmooth B) (hB' : IsSmooth B')
    (hSym : IsSymmetric B) (hND : IsNondegenerate B)
    (c : M) (x : E) (hx : x ∈ (chartAt E c).target) (i : I) :
    let S := symmetricMetricDirection
    let g := symmetricChartMetricComponents B c
    let h := originalChartPerturbation B B' c
    let G := metricComponents (coordinateBilinear B c) x
    deriv (fun t => originalChartEulerPath B B' c t x i) 0 =
      metricEulerJetLowerLinearization S G (assembleMetricComponents S (h x))
        (coordinateMetricFirstJet g x) (coordinateMetricFirstJet h x) (coordinateMetricSecondJet g x) i -
      ∑ a, ∑ s, metricActionCoefficient S (a, i) s G * coordinateMetricSecondJet h x a s := by
  intro S g h G
  have hg : ContDiffOn ℝ ∞ g (chartAt E c).target :=
    contDiffOn_pi.mpr (fun j => ManifoldBilinear.contDiffOn_metricComponents B hB c j.val.1 j.val.2)
  have hg' : ContDiffOn ℝ ∞ (symmetricChartMetricComponents B' c) (chartAt E c).target :=
    contDiffOn_pi.mpr (fun j => ManifoldBilinear.contDiffOn_metricComponents B' hB' c j.val.1 j.val.2)
  have hh : ContDiffOn ℝ ∞ h (chartAt E c).target := hg'.sub hg
  have hG : assembleMetricComponents S (g x) = G :=
    congrFun (assembledCoordinateMetric_symmetricChartMetricComponents B hSym c) x
  have hn : (assembleMetricComponents S (g x)).det ≠ 0 := by
    rw [hG]
    exact ManifoldVolumeRegularity.coordinate_det_ne_zero B hND c hx
  have he := linearizedCoordinateDensityEuler_eq_lower_sub_secondJet S g h
    (chartAt E c).open_target hg hh x hx hn i
  rw [hG] at he
  exact he

end Burnett.V03.Palatini
