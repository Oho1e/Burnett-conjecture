import Burnett.Analysis.TransportWard.Weyl.AffineProductSecondDerivative
import Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
import Burnett.Analysis.FrozenTransport.FrozenCubicCoefficientV03Bridge

set_option autoImplicit false
set_option maxHeartbeats 4700000
set_option maxRecDepth 4100

noncomputable section

namespace Burnett.V03.Palatini

open Filter Set Function Burnett.RicciSymbol Burnett.Geometry.ConnectionDifference
open Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

open private coordinateMetricFirstJet_line coordinateMetricSecondJet_line from Burnett.Analysis.FrozenTransport.V03EulerCoordinateJet
open private hasDerivAt_comp_fieldSegment from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

local notation "E₀" => CoordinateSpace

/-- The strong coordinate Euler quadratic variation has the two original
leading terms and an explicit error carrying at least one undifferentiated
perturbation and one background derivative. -/
theorem coordinateDensityEuler_secondAffineDerivative_eq_jets {ι : Type*} [Fintype ι]
    (S : ι → Mat) {U : Set E₀} (hU : IsOpen U) (g h : E₀ → ι → ℝ)
    (hg : ContDiffOn ℝ ∞ g U) (hh : ContDiffOn ℝ ∞ h U)
    (x : E₀) (hx : x ∈ U) (i : ι) (hG : (assembleMetricComponents S (g x)).det ≠ 0) :
    let G := assembleMetricComponents S (g x)
    let H := assembleMetricComponents S (h x)
    let p := coordinateMetricFirstJet g x
    let dp := coordinateMetricFirstJet h x
    let q := coordinateMetricSecondJet g x
    let dq := coordinateMetricSecondJet h x
    let L := metricEulerLowerCoefficient S i
    let C (a : Index) (s : ActionSlot ι) := metricActionCoefficient S (a,i) s
    deriv (deriv (fun u : ℝ => coordinateDensityEuler S (fun y => g y + u • h y) x i)) 0 =
      (∑ s, ∑ t, (secondFDeriv (L s t) G H H * p s * p t +
        2 * fderiv ℝ (L s t) G H * (dp s * p t + p s * dp t) + 2 * L s t G * dp s * dp t)) -
      (∑ a, ∑ s, (secondFDeriv (C a s) G H H * q a s + 2 * fderiv ℝ (C a s) G H * dq a s)) := by
  intro G H p dp q dq L C
  let F (t : ℝ) := coordinateDensityEuler S (fun y => g y + t • h y) x i
  let Q (s t : ActionSlot ι) (u : ℝ) := L s t (fieldSegment G H u) *
    (p s + u * dp s) * (p t + u * dp t)
  let P (a : Index) (s : ActionSlot ι) (u : ℝ) := C a s (fieldSegment G H u) * (q a s + u * dq a s)
  let J (u : ℝ) := (∑ s, ∑ t, Q s t u) - (∑ a, ∑ s, P a s u)
  have hOpen : IsOpen (fieldSegment G H ⁻¹' nonsingularMetricDomain) :=
    isOpen_nonsingularMetricDomain.preimage (continuous_const.add (continuous_id.smul continuous_const))
  have h0 : fieldSegment G H 0 ∈ nonsingularMetricDomain := by
    simpa only [fieldSegment, zero_smul, add_zero] using hG
  have hE : F =ᶠ[𝓝 (0 : ℝ)] J := by
    filter_upwards [hOpen.mem_nhds h0] with u hu
    have hDet : (assembleMetricComponents S (g x + u • h x)).det ≠ 0 := by
      simpa only [fieldSegment,G,H,map_add,map_smul] using hu
    have hDg := (hg.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have hDh := (hh.contDiffAt (hU.mem_nhds hx)).differentiableAt (by simp)
    have he := coordinateDensityEuler_eq_metricEulerAtJet S hU (fun y => g y + u • h y)
      (hg.add (hh.const_smul u)) x hx hDet i
    rw [coordinateMetricFirstJet_line g h x u hDg hDh,
      coordinateMetricSecondJet_line hU g h hg hh x hx u] at he
    simpa only [F,J,Q,P,metricEulerAtJet,C,L,p,dp,q,dq,G,H,fieldSegment,map_add,map_smul,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul] using he
  have hL (s t : ActionSlot ι) : ContDiffOn ℝ ∞ (L s t) nonsingularMetricDomain :=
    contDiffOn_metricEulerLowerCoefficient S i s t
  have hC (a : Index) (s : ActionSlot ι) : ContDiffOn ℝ ∞ (C a s) nonsingularMetricDomain :=
    contDiffOn_metricActionCoefficient S (a,i) s
  have hDer : deriv J =ᶠ[𝓝 (0 : ℝ)]
      (fun u => (∑ s, ∑ t, deriv (Q s t) u) - (∑ a, ∑ s, deriv (P a s) u)) := by
    filter_upwards [hOpen.mem_nhds h0] with u hu
    have hQ₀ (s t : ActionSlot ι) : DifferentiableAt ℝ (Q s t) u :=
      (((hasDerivAt_comp_fieldSegment _ isOpen_nonsingularMetricDomain (hL s t) G H u hu).mul
        (hasDerivAt_affine_real (p s) (dp s) u)).mul (hasDerivAt_affine_real (p t) (dp t) u)).differentiableAt
    have hP₀ (a : Index) (s : ActionSlot ι) : DifferentiableAt ℝ (P a s) u :=
      ((hasDerivAt_comp_fieldSegment _ isOpen_nonsingularMetricDomain (hC a s) G H u hu).mul
        (hasDerivAt_affine_real (q a s) (dq a s) u)).differentiableAt
    exact ((HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
      HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => (hQ₀ s t).hasDerivAt).sub
        (HasDerivAt.fun_sum fun a (_ : a ∈ Finset.univ) =>
          HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) => (hP₀ a s).hasDerivAt)).deriv
  have hQ₂ (s t : ActionSlot ι) := hasDerivAt_deriv_product_affine (L s t) isOpen_nonsingularMetricDomain
    (hL s t) G H hG (p s) (dp s) (p t) (dp t)
  have hP₂ (a : Index) (s : ActionSlot ι) : HasDerivAt (deriv (P a s))
      (secondFDeriv (C a s) G H H * q a s + 2 * fderiv ℝ (C a s) G H * dq a s) 0 := by
    simpa only [P, mul_zero, add_zero, zero_mul, zero_add, mul_one] using
      hasDerivAt_deriv_product_affine (C a s) isOpen_nonsingularMetricDomain
        (hC a s) G H hG (q a s) (dq a s) 1 0
  change deriv (deriv F) 0 = _
  rw [hE.deriv.deriv_eq, hDer.deriv_eq]
  exact ((HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) =>
    HasDerivAt.fun_sum fun t (_ : t ∈ Finset.univ) => hQ₂ s t).sub
      (HasDerivAt.fun_sum fun a (_ : a ∈ Finset.univ) =>
        HasDerivAt.fun_sum fun s (_ : s ∈ Finset.univ) => hP₂ a s)).deriv

/-- In the original ordered field coordinates the coefficient of two
perturbation first jets is exactly the negative of the frozen cubic array. -/
theorem metricEulerLowerCoefficient_ordered_eq_neg_frozenActionCubicQuadratic
    (G : Mat) (hG : G ∈ nonsingularMetricDomain) (a d : Index)
    (i j k : Burnett.Microlocal.PhysicalDensity.OrderedPair) :
    metricEulerLowerCoefficient Burnett.C02.frozenActionOrderedBasis k (a,i) (d,j) G =
      -Burnett.C02.frozenActionCubicQuadratic G a d i j k := by
  unfold metricEulerLowerCoefficient Burnett.C02.frozenActionCubicQuadratic
  rw [← Burnett.C02.frozenActionCubicLinear_eq_metricActionCoefficient_fderiv G hG a d k j i,
    ← Burnett.C02.frozenActionCubicLinear_eq_metricActionCoefficient_fderiv G hG a d i j k]
  ring

end Burnett.V03.Palatini
