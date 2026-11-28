import Burnett.Analysis.FrozenTransport.V03SegmentTaylor

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.V03.Palatini

open Set Filter
open scoped ContDiff Topology

open private hasDerivAt_comp_fieldSegment hasDerivAt_first_dir from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

theorem hasDerivAt_affine_real (p dp t : ℝ) : HasDerivAt (fun u => p + u * dp) dp t := by
  simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const dp).const_add p

theorem hasDerivAt_deriv_product_affine {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (C : V → ℝ) {U : Set V} (hU : IsOpen U) (hC : ContDiffOn ℝ ∞ C U) (G H : V) (hG : G ∈ U)
    (p dp q dq : ℝ) :
    HasDerivAt (deriv (fun t => C (fieldSegment G H t) * (p + t * dp) * (q + t * dq)))
      (secondFDeriv C G H H * p * q + 2 * fderiv ℝ C G H * (dp * q + p * dq) +
        2 * C G * dp * dq) 0 := by
  let a (t : ℝ) := C (fieldSegment G H t)
  let b (t : ℝ) := fderiv ℝ C (fieldSegment G H t) H
  let c (t : ℝ) := secondFDeriv C (fieldSegment G H t) H H
  let l (t : ℝ) := p + t * dp
  let r (t : ℝ) := q + t * dq
  let F (t : ℝ) := a t * l t * r t
  let dF (t : ℝ) := (b t * l t + a t * dp) * r t + a t * l t * dq
  have h0 : fieldSegment G H 0 ∈ U := by simpa only [fieldSegment, zero_smul, add_zero] using hG
  have hv (t : ℝ) (ht : fieldSegment G H t ∈ U) : HasDerivAt a (b t) t :=
    hasDerivAt_comp_fieldSegment C hU hC G H t ht
  have hNear : deriv F =ᶠ[𝓝 (0 : ℝ)] dF := by
    have hOpen : IsOpen (fieldSegment G H ⁻¹' U) :=
      hU.preimage (continuous_const.add (continuous_id.smul continuous_const))
    filter_upwards [hOpen.mem_nhds h0] with t ht
    exact (((hv t ht).mul (hasDerivAt_affine_real p dp t)).mul (hasDerivAt_affine_real q dq t)).deriv
  have hb : HasDerivAt b (c 0) 0 := hasDerivAt_first_dir C hU hC G H 0 h0
  have hl : HasDerivAt l dp 0 := hasDerivAt_affine_real p dp 0
  have hr : HasDerivAt r dq 0 := hasDerivAt_affine_real q dq 0
  have ha := hv 0 h0
  apply (((((hb.mul hl).add (ha.mul_const dp)).mul hr).add
      ((ha.mul hl).mul_const dq)).congr_of_eventuallyEq hNear).congr_deriv
  simp only [Pi.add_apply, Pi.mul_apply, a,b,c,l,r,fieldSegment,zero_smul,add_zero,zero_mul]
  ring

end Burnett.V03.Palatini
