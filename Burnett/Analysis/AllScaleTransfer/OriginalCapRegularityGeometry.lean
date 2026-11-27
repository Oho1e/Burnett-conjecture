import Burnett.Analysis.AllScaleTransfer.OriginalBranchRegularity

set_option autoImplicit false
set_option maxRecDepth 8500
set_option maxHeartbeats 9000000

noncomputable section

namespace Burnett.A05

open Filter Metric Set
open Burnett.A02.FrequencySplit Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped ContDiff BigOperators Topology

/-- A genuine nonzero point in the closure of one localized symbol has
an open neighborhood with all three slots in that same enlarged cap. -/
theorem eventually_enlargedCap_of_mem_tsupport_capLocalizedNearSymbol
    {metric : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D) (hη : 0 ≤ η) (hIO : inner ≤ outer)
    (m : Joint → ℂ) (adj : AnalyticNearAdjacentSupport metric δ η inner m)
    (γ : ↑S.centers) {p : Joint} (hp : p ∈ nonzeroSignedTriads)
    (hSupport : p ∈ tsupport (capLocalizedNearSymbol S m γ)) :
    let K := tsupport (enlargedCapMultiplier metric δ η outer enlarged γ)
    ∀ᶠ z in 𝓝 p, z.1 ∈ K ∧ z.2 ∈ K ∧ -(z.1+z.2) ∈ K := by
  let Q := enlargedCapMultiplier metric δ η outer enlarged (γ : Vec)
  have onSource {z : Joint} (hz : z ∈ nonzeroSignedTriads) (ha : capLocalizedNearSymbol S m γ z ≠ 0) :
      Q z.1 = 1 ∧ Q z.2 = 1 ∧ Q (-(z.1+z.2)) = 1 := by
    have hm : m z ≠ 0 := right_ne_zero_of_mul ha
    have hcap := Complex.ofReal_ne_zero.mp (left_ne_zero_of_mul ha)
    obtain ⟨_,thin₂,thin₃,edge₂,edge₃⟩ := adj z hm hz.1 hz.2.1 hz.2.2
    have widen (r : E) (hr : InRelativeCone metric (inner*η) r) :
        |quadratic metric r| ≤ outer*η*‖r‖^2 :=
      hr.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hIO hη) (sq_nonneg _))
    exact S.enlarged_on_three_nearSlots γ γ.property z.1 z.2 (-(z.1+z.2)) hz.1 hz.2.1 hz.2.2
      (subset_tsupport _ hcap) edge₂ edge₃ (widen _ thin₂) (widen _ thin₃)
  have contQ {x : E} (hx : x ≠ 0) : ContinuousAt Q x :=
    (((S.smoothness γ γ.property).2).continuousOn x hx).continuousAt
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)
  have slotEventually (f : Joint → E) (hf : Continuous f) (hfx : f p ≠ 0)
      (one : ∀ z ∈ nonzeroSignedTriads, capLocalizedNearSymbol S m γ z ≠ 0 → Q (f z) = 1) :
      ∀ᶠ z in 𝓝 p, f z ∈ tsupport Q := by
    have cont : ContinuousAt (Q ∘ f) p := (contQ hfx).comp hf.continuousAt
    have atP : Q (f p) = 1 := by
      by_contra hn
      apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hSupport
      filter_upwards [isOpen_nonzeroSignedTriads.mem_nhds hp,cont.eventually_ne hn] with z hz hneq
      exact not_ne_iff.mp (fun h => hneq (one z hz h))
    have nz : Q (f p) ≠ 0 := by rw [atP]; exact one_ne_zero
    filter_upwards [cont.eventually_ne nz] with z hz
    exact subset_tsupport _ hz
  exact (slotEventually _ continuous_fst hp.1 (fun _ hz hs => (onSource hz hs).1)).and
    ((slotEventually _ continuous_snd hp.2.1 (fun _ hz hs => (onSource hz hs).2.1)).and
      (slotEventually _ (continuous_fst.add continuous_snd).neg hp.2.2 (fun _ hz hs => (onSource hz hs).2.2)))

/-- On the nonzero signed triads, the actual cap partition reconstructs
the unweighted original symbol pointwise. -/
theorem capLocalizedNearSymbol_sum_on_nonzeroSignedTriads
    {metric : Form} {δ η inner outer enlarged D : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (m : Joint → ℂ) (adj : AnalyticNearAdjacentSupport metric δ η inner m)
    {p : Joint} (hp : p ∈ nonzeroSignedTriads) :
    ∑ γ : ↑S.centers, capLocalizedNearSymbol S m γ p = m p := by
  simp only [capLocalizedNearSymbol,← Finset.sum_mul]
  by_cases hm : m p = 0
  · rw [hm,mul_zero]
  have hCone := (adj p hm hp.1 hp.2.1 hp.2.2).1
  rw [← Complex.ofReal_sum,Finset.univ_eq_attach,
    Finset.sum_attach S.centers (fun w => capMultiplier S.centers metric δ η inner outer w p.1),
    S.partition_inner p.1 hp.1 hCone,Complex.ofReal_one,one_mul]

/-- The normalized variables of the actual enlarged cap supply a radius
for all four signed charts and a uniform interval of comparable offsets. -/
theorem exists_analyticNearCap_atlas_coverage {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube outer enlarged : ℝ) (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) :
    ∃ (R : ℝ) (N : ℕ), 0 < R ∧ R < 1 ∧
      ∀ (metric : Form) (w : Vec) (F : NullCapChart metric w),
        ‖w‖ = 1 → ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), 4*B*(5*δ) ≤ 1 →
        let a := capFrequencyEquiv F hδ.ne'
        let K := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged w)
        (∀ z : E, z ≠ 0 → a z ∈ K → (endpointDirection z) 0 ≠ 0 ∧
          endpointTail (endpointDirection z) ∈ ball (0 : EndpointAngle) R) ∧
        ∀ p ∈ nonzeroSignedTriads, a p.1 ∈ K → a p.2 ∈ K → a (-(p.1+p.2)) ∈ K →
          comparableSlotWeight ϑ κ (a p.1) (a p.2) (a (-(p.1+p.2))) ≠ 0 →
          ∃ j k : ℤ, k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ∧
            integerRadialWindow (j+k) p.1 ≠ 0 ∧ integerRadialWindow j p.2 ≠ 0 := by
  classical
  obtain ⟨α,hα,hα₁,axis⟩ := exists_enlarged_cap_support_axial_margin B tube outer enlarged hB hTube hOut hOE
  obtain ⟨r,R,hr,hrR,hR,tails⟩ := exists_endpointTail_radii hα hα₁
  obtain ⟨L,U,hL,hU,compare⟩ := exists_uniform_capFrequency_norm_compare B tube outer enlarged hB hTube hOut hOE
  obtain ⟨N,shifts⟩ := exists_comparable_integerRadialWindow_finiteShifts hCut hFlat κ L U hκ hκsmall hL hU
  refine ⟨R,N,hr.trans hrR,hR,?_⟩
  intro metric w F hw hF δ hδ hsmall a K
  refine ⟨?_,?_⟩
  · intro z hz hK
    have axial := axis metric w F hw hF δ hδ hsmall z hK
    have npos := norm_pos_iff.mpr hz
    have unit : α ≤ |endpointDirection z 0| := by
      change α ≤ |‖z‖⁻¹ * z 0|
      rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr npos.le),inv_mul_eq_div]
      exact (le_div_iff₀ npos).mpr axial
    exact ⟨abs_pos.mp (hα.trans_le unit),
      mem_ball_zero_iff.mpr ((tails _ (endpointDirection_mem_sphere hz) unit).trans_lt hrR)⟩
  · intro p hp hp₁ hp₂ hp₃ active
    obtain ⟨j,hj⟩ : ∃ j : ℤ, integerRadialWindow j p.2 ≠ 0 := by
      by_contra! hZero
      have h := (integerRadialWindow_hasSum p.2).tsum_eq
      rw [if_neg hp.2.1] at h
      simp only [hZero,tsum_zero] at h
      exact zero_ne_one h
    have hNorm := compare metric w F hw hF δ hδ hsmall
    have cover := (shifts a p.1 p.2 j hj active (hNorm p.1 hp₁) (hNorm p.2 hp₂)
      (hNorm (-(p.1+p.2)) hp₃)).2.1
    obtain ⟨k,hk,hk₁⟩ : ∃ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), integerRadialWindow (j+k) p.1 ≠ 0 := by
      by_contra! hZero
      rw [Finset.sum_eq_zero hZero] at cover
      exact zero_ne_one cover
    exact ⟨j,k,hk,hk₁,hj⟩

end Burnett.A05

#print axioms Burnett.A05.eventually_enlargedCap_of_mem_tsupport_capLocalizedNearSymbol
#print axioms Burnett.A05.capLocalizedNearSymbol_sum_on_nonzeroSignedTriads
#print axioms Burnett.A05.exists_analyticNearCap_atlas_coverage
