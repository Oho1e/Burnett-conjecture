import Burnett.Analysis.FrozenTransport.V03MetricActionCoefficient

/-! The actual finite-coordinate Euler polynomial and its quadratic Taylor defect
along one common field and jet variation. -/

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option maxRecDepth 3500
set_option synthInstance.maxSize 4000

noncomputable section

namespace Burnett.V03

open Filter Set Burnett.Analysis.TransportWardSymbol
open scoped BigOperators ContDiff Matrix.Norms.Elementwise Topology

/-- Subtract the value, first variation, and one-half the second variation of a
real one-parameter Euler expression. -/
def quadraticPathRemainder (f : ℝ → ℝ) : ℝ :=
  f 1 - f 0 - deriv f 0 - (1 / 2) * deriv (deriv f) 0

private theorem quadraticPathRemainder_sub {U : Set ℝ} (hU : IsOpen U) (h0 : 0 ∈ U)
    {f g : ℝ → ℝ} (hf : ContDiffOn ℝ ∞ f U) (hg : ContDiffOn ℝ ∞ g U) :
    quadraticPathRemainder (fun t => f t - g t) =
      quadraticPathRemainder f - quadraticPathRemainder g := by
  have h₁ (t : ℝ) (ht : t ∈ U) : deriv (fun u => f u - g u) t = deriv f t - deriv g t :=
    deriv_fun_sub ((hf.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp))
      ((hg.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp))
  have hNear : deriv (fun u => f u - g u) =ᶠ[𝓝 (0 : ℝ)] fun u => deriv f u - deriv g u := by
    filter_upwards [hU.mem_nhds h0] with t ht
    exact h₁ t ht
  have h₂ : deriv (fun u => deriv f u - deriv g u) 0 = deriv (deriv f) 0 - deriv (deriv g) 0 :=
    deriv_fun_sub
      (((hf.deriv_of_isOpen hU (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).contDiffAt
        (hU.mem_nhds h0)).differentiableAt (by simp))
      (((hg.deriv_of_isOpen hU (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).contDiffAt
        (hU.mem_nhds h0)).differentiableAt (by simp))
  simp only [quadraticPathRemainder, hNear.deriv_eq, h₁ 0 h0, h₂]
  ring

private theorem quadraticPathRemainder_sum {ι : Type*} [Fintype ι]
    {U : Set ℝ} (hU : IsOpen U) (h0 : 0 ∈ U) (f : ι → ℝ → ℝ)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) U) :
    quadraticPathRemainder (fun t => ∑ i, f i t) = ∑ i, quadraticPathRemainder (f i) := by
  have h₁ (t : ℝ) (ht : t ∈ U) : deriv (fun u => ∑ i, f i u) t = ∑ i, deriv (f i) t :=
    deriv_fun_sum fun i _ => ((hf i).contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
  have hNear : deriv (fun u => ∑ i, f i u) =ᶠ[𝓝 (0 : ℝ)] fun u => ∑ i, deriv (f i) u := by
    filter_upwards [hU.mem_nhds h0] with t ht
    exact h₁ t ht
  have h₂ : deriv (fun u => ∑ i, deriv (f i) u) 0 = ∑ i, deriv (deriv (f i)) 0 :=
    deriv_fun_sum fun i _ => (((hf i).deriv_of_isOpen hU
      (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).contDiffAt (hU.mem_nhds h0)).differentiableAt (by simp)
  simp only [quadraticPathRemainder, h₁ 0 h0, hNear.deriv_eq, h₂, Finset.mul_sum, ← Finset.sum_sub_distrib]

section Scalar

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private theorem contDiff_fieldSegment (g h : V) : ContDiff ℝ ∞ (fieldSegment g h) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

private theorem hasDerivAt_affine_scalar (a b t : ℝ) :
    HasDerivAt (fun u => a + u * b) b t := by
  simpa only [id_eq, one_mul] using ((hasDerivAt_id t).mul_const b).const_add a

open private hasDerivAt_comp_fieldSegment hasDerivAt_first_dir from Burnett.Analysis.FrozenTransport.V03SegmentTaylor

/-- Exact coefficient defects of a quadratic first-jet monomial. -/
theorem quadraticPathRemainder_mul_two_affine (F : V → ℝ) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V) (hg : g ∈ U)
    (p dp q dq : ℝ) :
    quadraticPathRemainder (fun t => F (fieldSegment g h t) * (p + t * dp) * (q + t * dq)) =
      quadraticTaylorRemainder F g h * p * q +
      linearTaylorRemainder F g h * (dp * q + p * dq) +
      (F (g + h) - F g) * dp * dq := by
  let a (t : ℝ) := F (fieldSegment g h t)
  let b (t : ℝ) := fderiv ℝ F (fieldSegment g h t) h
  let c (t : ℝ) := secondFDeriv F (fieldSegment g h t) h h
  let ℓ (t : ℝ) := p + t * dp
  let r (t : ℝ) := q + t * dq
  let B (t : ℝ) := a t * ℓ t * r t
  let D (t : ℝ) := (b t * ℓ t + a t * dp) * r t + (a t * ℓ t) * dq
  have h0 : fieldSegment g h 0 ∈ U := by simpa only [fieldSegment, zero_smul, add_zero] using hg
  have hA (t : ℝ) (ht : fieldSegment g h t ∈ U) : HasDerivAt a (b t) t :=
    hasDerivAt_comp_fieldSegment F hU hF g h t ht
  have hB (t : ℝ) (ht : fieldSegment g h t ∈ U) : HasDerivAt B (D t) t :=
    ((hA t ht).mul (hasDerivAt_affine_scalar p dp t)).mul (hasDerivAt_affine_scalar q dq t)
  have hNear : deriv B =ᶠ[𝓝 (0 : ℝ)] D := by
    have hOpen : IsOpen (fieldSegment g h ⁻¹' U) :=
      hU.preimage (contDiff_fieldSegment g h).continuous
    filter_upwards [hOpen.mem_nhds h0] with t ht
    exact (hB t ht).deriv
  have ha := hA 0 h0
  have hb : HasDerivAt b (c 0) 0 := hasDerivAt_first_dir F hU hF g h 0 h0
  have hl : HasDerivAt ℓ dp 0 := hasDerivAt_affine_scalar p dp 0
  have hr : HasDerivAt r dq 0 := hasDerivAt_affine_scalar q dq 0
  have hD := (((hb.mul hl).add (ha.mul_const dp)).mul hr).add ((ha.mul hl).mul_const dq)
  change quadraticPathRemainder B = _
  rw [quadraticPathRemainder, (hB 0 h0).deriv, hNear.deriv_eq]
  rw [show deriv D 0 = _ from hD.deriv]
  simp only [Pi.add_apply, Pi.mul_apply, a, b, c, ℓ, r, B, D, fieldSegment,
    zero_smul, one_smul, add_zero, zero_mul, one_mul,
    quadraticTaylorRemainder, linearTaylorRemainder, smul_eq_mul]
  ring

private theorem quadraticPathRemainder_mul_one_affine (F : V → ℝ) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V) (hg : g ∈ U) (p dp : ℝ) :
    quadraticPathRemainder (fun t => F (fieldSegment g h t) * (p + t * dp)) =
      quadraticTaylorRemainder F g h * p + linearTaylorRemainder F g h * dp := by
  simpa using quadraticPathRemainder_mul_two_affine F hU hF g h hg p dp 1 0

end Scalar

/-- Field derivative coefficient of the two first jets after expanding the
Euler divergence by the product rule. -/
def metricEulerLowerCoefficient {ι : Type*} (S : ι → Mat) (i : ι)
    (s t : ActionSlot ι) (G : Mat) : ℝ :=
  -(fderiv ℝ (metricActionCoefficient S (s.1, i) t) G (S s.2)) +
    (1 / 2) * fderiv ℝ (metricActionCoefficient S s t) G (S i)

theorem contDiffOn_metricEulerLowerCoefficient {ι : Type*} (S : ι → Mat)
    (i : ι) (s t : ActionSlot ι) :
    ContDiffOn ℝ ∞ (metricEulerLowerCoefficient S i s t) nonsingularMetricDomain := by
  have hd (a b : ActionSlot ι) (w : Mat) :
      ContDiffOn ℝ ∞ (fun G => fderiv ℝ (metricActionCoefficient S a b) G w) nonsingularMetricDomain :=
    ((contDiffOn_metricActionCoefficient S a b).fderiv_of_isOpen
      isOpen_nonsingularMetricDomain (by simp)).clm_apply contDiffOn_const
  exact (hd (s.1, i) t (S s.2)).neg.add (contDiffOn_const.mul (hd s t (S i)))

/-- Coordinate Euler density in its expanded second-jet form, with all entries
taken from the actual Gamma–Gamma coefficients. -/
def metricEulerAtJet {ι : Type*} [Fintype ι] (S : ι → Mat) (G : Mat)
    (p : ActionSlot ι → ℝ) (q : Fin 4 → ActionSlot ι → ℝ) (i : ι) : ℝ :=
  (∑ s, ∑ t, metricEulerLowerCoefficient S i s t G * p s * p t) -
    ∑ a, ∑ t, metricActionCoefficient S (a, i) t G * q a t

/-- The lower remainder contains the second jet of the background and the two
first jets. The perturbation's second jet lies wholly in the principal term. -/
def metricEulerJetLowerRemainder {ι : Type*} [Fintype ι] (S : ι → Mat) (g h : Mat)
    (p dp : ActionSlot ι → ℝ) (q : Fin 4 → ActionSlot ι → ℝ) (i : ι) : ℝ :=
  (∑ s, ∑ t,
    let F := metricEulerLowerCoefficient S i s t
    quadraticTaylorRemainder F g h * p s * p t +
      linearTaylorRemainder F g h * (dp s * p t + p s * dp t) +
      (F (g + h) - F g) * dp s * dp t) -
    ∑ a, ∑ t, quadraticTaylorRemainder (metricActionCoefficient S (a, i) t) g h * q a t

/-- Taylor expansion of the actual Euler jet polynomial along one common
variation in the field, its first jet, and its second jet. -/
theorem metricEulerJetRemainder_eq {ι : Type*} [Fintype ι] (S : ι → Mat) (g h : Mat)
    (p dp : ActionSlot ι → ℝ) (q dq : Fin 4 → ActionSlot ι → ℝ) (i : ι) (hg : g.det ≠ 0) :
    quadraticPathRemainder (fun u =>
      metricEulerAtJet S (fieldSegment g h u) (fieldSegment p dp u) (fieldSegment q dq u) i) =
      (∑ a, ∑ t, principalCoefficientRemainder (metricActionCoefficient S (a, i) t) g h * dq a t) +
        metricEulerJetLowerRemainder S g h p dp q i := by
  let U := fieldSegment g h ⁻¹' nonsingularMetricDomain
  have hU : IsOpen U := isOpen_nonsingularMetricDomain.preimage (contDiff_fieldSegment g h).continuous
  have h0 : 0 ∈ U := by simpa only [U, mem_preimage, fieldSegment, zero_smul, add_zero] using hg
  let P (a : Fin 4) (t : ActionSlot ι) (u : ℝ) :=
    metricActionCoefficient S (a, i) t (fieldSegment g h u) * (q a t + u * dq a t)
  let L (s t : ActionSlot ι) (u : ℝ) :=
    metricEulerLowerCoefficient S i s t (fieldSegment g h u) *
      (p s + u * dp s) * (p t + u * dp t)
  have hsmooth (c d : ℝ) : ContDiffOn ℝ ∞ (fun u => c + u * d) U :=
    (contDiff_const.add ((contDiff_id : ContDiff ℝ ∞ (id : ℝ → ℝ)).mul contDiff_const)).contDiffOn
  have hP (a t) : ContDiffOn ℝ ∞ (P a t) U :=
    ((contDiffOn_metricActionCoefficient S (a, i) t).comp
      (contDiff_fieldSegment g h).contDiffOn (fun _ hu => hu)).mul (hsmooth _ _)
  have hL (s t) : ContDiffOn ℝ ∞ (L s t) U :=
    (((contDiffOn_metricEulerLowerCoefficient S i s t).comp
      (contDiff_fieldSegment g h).contDiffOn (fun _ hu => hu)).mul (hsmooth _ _)).mul (hsmooth _ _)
  have he : (fun u => metricEulerAtJet S (fieldSegment g h u) (fieldSegment p dp u)
      (fieldSegment q dq u) i) = fun u => (∑ s, ∑ t, L s t u) - ∑ a, ∑ t, P a t u := by
    funext u
    simp only [metricEulerAtJet, fieldSegment, Pi.add_apply, Pi.smul_apply, smul_eq_mul, P, L]
  have hPsum : quadraticPathRemainder (fun u => ∑ a, ∑ t, P a t u) =
      ∑ a, ∑ t, quadraticPathRemainder (P a t) := by
    rw [quadraticPathRemainder_sum hU h0 _ (fun a => ContDiffOn.sum fun t _ => hP a t)]
    apply Finset.sum_congr rfl
    intro a _
    exact quadraticPathRemainder_sum hU h0 _ (hP a)
  have hLsum : quadraticPathRemainder (fun u => ∑ s, ∑ t, L s t u) =
      ∑ s, ∑ t, quadraticPathRemainder (L s t) := by
    rw [quadraticPathRemainder_sum hU h0 _ (fun s => ContDiffOn.sum fun t _ => hL s t)]
    apply Finset.sum_congr rfl
    intro s _
    exact quadraticPathRemainder_sum hU h0 _ (hL s)
  have hp (a t) : quadraticPathRemainder (P a t) =
      quadraticTaylorRemainder (metricActionCoefficient S (a, i) t) g h * q a t +
        linearTaylorRemainder (metricActionCoefficient S (a, i) t) g h * dq a t :=
    quadraticPathRemainder_mul_one_affine _ isOpen_nonsingularMetricDomain
      (contDiffOn_metricActionCoefficient S (a, i) t) g h hg _ _
  have hl (s t) : quadraticPathRemainder (L s t) =
      quadraticTaylorRemainder (metricEulerLowerCoefficient S i s t) g h * p s * p t +
      linearTaylorRemainder (metricEulerLowerCoefficient S i s t) g h * (dp s * p t + p s * dp t) +
      (metricEulerLowerCoefficient S i s t (g + h) - metricEulerLowerCoefficient S i s t g) *
        dp s * dp t :=
    quadraticPathRemainder_mul_two_affine _ isOpen_nonsingularMetricDomain
      (contDiffOn_metricEulerLowerCoefficient S i s t) g h hg _ _ _ _
  rw [he, quadraticPathRemainder_sub hU h0
    (ContDiffOn.sum fun s _ => ContDiffOn.sum fun t _ => hL s t)
    (ContDiffOn.sum fun a _ => ContDiffOn.sum fun t _ => hP a t),
    hPsum, hLsum]
  simp only [hp, hl, metricEulerJetLowerRemainder, principalCoefficientRemainder, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  ring

end Burnett.V03
