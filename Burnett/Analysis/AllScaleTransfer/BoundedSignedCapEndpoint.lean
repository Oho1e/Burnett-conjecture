import Burnett.Analysis.AllScaleTransfer.AnalyticNearData

set_option autoImplicit false
set_option maxRecDepth 6300
set_option maxHeartbeats 6300000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit Burnett.A05.BoxFourier Burnett.C02
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.Analysis.LowRatio (Angles)
open scoped ContDiff Topology

open private continuous_signedAxis from Burnett.Analysis.AllScaleTransfer.SignedAnnularCharts

private def capEndpointAngles (p : Joint) : Angles := (endpointTail p.1, endpointTail p.2)

private def capEndpointUnitDomain (R : ℝ) : Set Joint :=
  (sphere (0 : E) 1 ×ˢ sphere (0 : E) 1) ∩ capEndpointAngles ⁻¹' capCorrectionAngles R

private def capEndpointSignedDomain (R : ℝ) (s : CapSigns) : Set Joint :=
  capEndpointUnitDomain R ∩ {p | 0 < signedAxis s.1 p.1 ∧ 0 < signedAxis s.2 p.2}

private theorem continuous_capEndpointAngles : Continuous capEndpointAngles :=
  (endpointTail.continuous.comp continuous_fst).prodMk (endpointTail.continuous.comp continuous_snd)

private theorem measurableSet_capEndpointSignedDomain (R : ℝ) (s : CapSigns) :
    MeasurableSet (capEndpointSignedDomain R s) := by
  have hAngle : IsOpen (capCorrectionAngles R) := isOpen_ball.prod isOpen_ball
  have hSign₁ : IsOpen {p : Joint | 0 < signedAxis s.1 p.1} :=
    isOpen_lt continuous_const ((continuous_signedAxis s.1).comp continuous_fst)
  have hSign₂ : IsOpen {p : Joint | 0 < signedAxis s.2 p.2} :=
    isOpen_lt continuous_const ((continuous_signedAxis s.2).comp continuous_snd)
  have hSphere : MeasurableSet (sphere (0 : E) 1) := isClosed_sphere.measurableSet
  exact ((hSphere.prod hSphere).inter
    (hAngle.measurableSet.preimage continuous_capEndpointAngles.measurable)).inter
      (hSign₁.measurableSet.inter hSign₂.measurableSet)

private theorem existsUnique_positive_signedAxis {x : E} (hx : 0 < |x 0|) :
    ∃! s : Bool, 0 < signedAxis s x := by
  by_cases hp : 0 < x 0
  · refine ⟨true, hp, ?_⟩
    intro s hs
    cases s
    · exact (not_lt_of_ge (neg_nonpos.mpr hp.le) hs).elim
    · rfl
  · have hn : x 0 < 0 := lt_of_le_of_ne (le_of_not_gt hp) (abs_pos.mp hx)
    refine ⟨false, neg_pos.mpr hn, ?_⟩
    intro s hs
    cases s
    · rfl
    · exact (not_lt_of_ge hn.le hs).elim

private theorem existsUnique_capEndpointSignedDomain {R : ℝ} (hR : R < 1)
    {p : Joint} (hp : p ∈ capEndpointUnitDomain R) :
    ∃! s : CapSigns, p ∈ capEndpointSignedDomain R s := by
  have axis {x : E} (hx : x ∈ sphere (0 : E) 1) (hu : endpointTail x ∈ ball (0 : EndpointAngle) R) :
      0 < |x 0| := by
    have hn : ‖endpointTail x‖ < 1 := (mem_ball_zero_iff.mp hu).trans hR
    have hsq : ‖endpointTail x‖^2 < (1 : ℝ)^2 := (sq_lt_sq₀ (norm_nonneg _) zero_le_one).mpr hn
    rw [endpointTail_head_abs hx]
    exact Real.sqrt_pos.2 (sub_pos.mpr (by simpa only [one_pow] using hsq))
  obtain ⟨s, hs, hsu⟩ := existsUnique_positive_signedAxis (axis hp.1.1 hp.2.1)
  obtain ⟨t, ht, htu⟩ := existsUnique_positive_signedAxis (axis hp.1.2 hp.2.2)
  exact ⟨(s, t), ⟨hp, hs, ht⟩, fun r hr => Prod.ext (hsu _ hr.2.1) (htu _ hr.2.2)⟩

private theorem capEndpointSignedDomain_readback (M : E → E → ℝ → ℂ)
    {R : ℝ} {s : CapSigns} {p : Joint} (hp : p ∈ capEndpointSignedDomain R s) :
    signedEndpointProfile M s (capEndpointAngles p, 0) = M p.1 p.2 0 := by
  unfold signedEndpointProfile capEndpointAngles
  rw [signedChartLift_endpointTail s.1 hp.1.1.1 hp.2.1, signedChartLift_endpointTail s.2 hp.1.1.2 hp.2.2]

/-- Extend the actual zero-ratio endpoint to a function on all pairs of
frequencies by zero outside the two unit spheres and chart angular balls. -/
def boundedCapEndpointTrace (R : ℝ) (M : E → E → ℝ → ℂ) (p : Joint) : ℂ := by
  classical
  exact if p ∈ capEndpointUnitDomain R then M p.1 p.2 0 else 0

private theorem measurable_boundedCapEndpointTrace {R b : ℝ} (hR : R < 1) (hb : 0 < b)
    (M : E → E → ℝ → ℂ)
    (smooth : ∀ s : CapSigns, ContDiffOn ℝ 100 (signedEndpointProfile M s)
      (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) :
    Measurable (boundedCapEndpointTrace R M) := by
  classical
  let F (s : CapSigns) : Joint → ℂ := (capEndpointSignedDomain R s).piecewise
    (fun p => signedEndpointProfile M s (capEndpointAngles p, 0)) 0
  have measurable (s : CapSigns) : Measurable (F s) := by
    have hc : Continuous (fun p : Joint => (capEndpointAngles p, (0 : ℝ))) :=
      continuous_capEndpointAngles.prodMk continuous_const
    have hf : ContinuousOn (fun p : Joint => signedEndpointProfile M s (capEndpointAngles p, 0))
        (capEndpointSignedDomain R s) :=
      (smooth s).continuousOn.comp hc.continuousOn (fun p hp => ⟨hp.1.2, le_rfl, hb⟩)
    exact hf.measurable_piecewise continuousOn_const (measurableSet_capEndpointSignedDomain R s)
  have hSum : Measurable (fun p : Joint => ∑ s : CapSigns, F s p) :=
    Finset.univ.measurable_fun_sum (fun s _ => measurable s)
  have hEq : (fun p : Joint => ∑ s : CapSigns, F s p) = boundedCapEndpointTrace R M := by
    funext p
    by_cases hp : p ∈ capEndpointUnitDomain R
    · obtain ⟨s, hs, huni⟩ := existsUnique_capEndpointSignedDomain hR hp
      rw [Finset.sum_eq_single s]
      · simp only [F, Set.piecewise, if_pos hs, boundedCapEndpointTrace, if_pos hp]
        exact capEndpointSignedDomain_readback M hs
      · intro t _ ht
        have hnot : p ∉ capEndpointSignedDomain R t := fun h => ht (huni t h)
        change (if p ∈ capEndpointSignedDomain R t then signedEndpointProfile M t (capEndpointAngles p, 0) else 0) = 0
        exact if_neg hnot
      · simp
    · have hnone (s : CapSigns) : p ∉ capEndpointSignedDomain R s := fun h => hp h.1
      simp [F, hnone, boundedCapEndpointTrace, hp]
  exact hEq ▸ hSum

private theorem norm_boundedCapEndpointTrace_le {R b A : ℝ} (hR : R < 1) (hb : 0 < b) (hA : 0 ≤ A)
    (M : E → E → ℝ → ℂ) (p : Joint)
    (jets : ∀ (s : CapSigns) n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) :
    ‖boundedCapEndpointTrace R M p‖ ≤ A := by
  classical
  by_cases hp : p ∈ capEndpointUnitDomain R
  · obtain ⟨s, hs, _⟩ := existsUnique_capEndpointSignedDomain hR hp
    rw [boundedCapEndpointTrace, if_pos hp, ← capEndpointSignedDomain_readback M hs]
    simpa only [norm_iteratedFDerivWithin_zero] using jets s 0 (by norm_num) (capEndpointAngles p, 0) ⟨hp.2, le_rfl, hb⟩
  · simpa only [boundedCapEndpointTrace, if_neg hp, norm_zero] using hA

private theorem signedChartLift_pair_mem_capEndpointUnitDomain {R : ℝ} (hR : R < 1)
    (s : CapSigns) {u : Angles} (hu : u ∈ capCorrectionAngles R) :
    (signedChartLift s.1 u.1, signedChartLift s.2 u.2) ∈ capEndpointUnitDomain R := by
  have h₁ : ‖u.1‖ < 1 := (mem_ball_zero_iff.mp hu.1).trans hR
  have h₂ : ‖u.2‖ < 1 := (mem_ball_zero_iff.mp hu.2).trans hR
  refine ⟨⟨(signedChartLift_unitSphere s.1 h₁).1, (signedChartLift_unitSphere s.2 h₂).1⟩, ?_⟩
  change (endpointTail (signedChartLift s.1 u.1), endpointTail (signedChartLift s.2 u.2)) ∈ capCorrectionAngles R
  simpa only [endpointTail_signedChartLift] using hu

/-- Replace only the zero-ratio ambient values. The four chart profiles
agree throughout the one-sided chart domains, including the actual traces. -/
theorem exists_bounded_measurable_signedCapEndpoint_profiles {R b A : ℝ}
    (hR : R < 1) (hb : 0 < b) (hA : 0 ≤ A) (M : Fin 3 → E → E → ℝ → ℂ)
    (smooth : ∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s)
      (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b))
    (jets : ∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) :
    ∃ M' : Fin 3 → E → E → ℝ → ℂ,
      (∀ i, Measurable (fun p : Joint => M' i p.1 p.2 0)) ∧
      (∀ i (p : Joint), ‖M' i p.1 p.2 0‖ ≤ A) ∧
      (∀ i x y t, t ≠ 0 → M' i x y t = M i x y t) ∧
      (∀ i s, EqOn (signedEndpointProfile (M' i) s) (signedEndpointProfile (M i) s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
      (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M' i) s)
        (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
      ∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M' i) s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A := by
  classical
  let M' (i : Fin 3) (x y : E) (t : ℝ) :=
    if t = 0 then boundedCapEndpointTrace R (M i) (x, y) else M i x y t
  have agree (i : Fin 3) (s : CapSigns) : EqOn (signedEndpointProfile (M' i) s) (signedEndpointProfile (M i) s)
      (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) := by
    intro z hz
    by_cases ht : z.2 = 0
    · have hPair := signedChartLift_pair_mem_capEndpointUnitDomain hR s hz.1
      simp only [signedEndpointProfile, M']
      rw [if_pos ht, boundedCapEndpointTrace, if_pos hPair, ht]
    · simp only [signedEndpointProfile, M', if_neg ht]
  refine ⟨M', ?_, ?_, ?_, agree, fun i s => (smooth i s).congr (agree i s), ?_⟩
  · intro i
    simpa only [M', if_true] using measurable_boundedCapEndpointTrace hR hb (M i) (smooth i)
  · intro i p
    simpa only [M', if_true] using norm_boundedCapEndpointTrace_le hR hb hA (M i) p (jets i)
  · intro i x y t ht
    simp only [M', if_neg ht]
  · intro i s n hn z hz
    simpa only [iteratedFDerivWithin_congr (agree i s) hz n] using jets i s n hn z hz

/-- The one-sided signed chart data and the original positive ratios supply
the cap budget. No global assumption on the unextended zero-ratio values
is required. -/
theorem analyticNearCapBudget_of_signed_profiles
    (ϑ : ℝ → ℝ) (κ b R A : ℝ) (N : ℕ)
    {metric : Form} {δ η inner outer enlarged D : ℝ} (hδ : δ ≠ 0)
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (chart : ∀ γ : ↑S.centers, NullCapChart metric γ) (m : Joint → ℂ)
    (hR : R < 1) (hb : 0 < b) (hA : 0 ≤ A)
    (source : ∀ γ : ↑S.centers,
      let a := capFrequencyEquiv (chart γ) hδ
      let K := tsupport (enlargedCapMultiplier metric δ η outer enlarged γ)
      let mγ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
      let low (i : Fin 3) := radianFourBranchSymbol ϑ κ (radianLowSlotView mγ i) 0 ∘ pairedFrequencyEquiv a
      let comparable := radianFourBranchSymbol ϑ κ mγ 3 ∘ pairedFrequencyEquiv a
      (∃ M : Fin 3 → E → E → ℝ → ℂ,
        (∀ i s, ContDiffOn ℝ 100 (signedEndpointProfile (M i) s)
          (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b)) ∧
        (∀ i s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
          ‖iteratedFDerivWithin ℝ n (signedEndpointProfile (M i) s)
            (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A) ∧
        ∀ (i : Fin 3) (p : Joint), a p.1 ∈ K → a p.2 ∈ K → a (-(p.1+p.2)) ∈ K →
          ‖a p.1‖/‖a p.2‖ ∈ Ioo (0 : ℝ) b →
            low i p = M i (endpointDirection p.1) (endpointDirection p.2) (‖a p.1‖/‖a p.2‖)) ∧
        AnalyticNearComparableBudget N A comparable) : AnalyticNearCapBudget ϑ κ b R A N hδ S chart m := by
  intro γ a K mγ low comparable
  obtain ⟨⟨M, smooth, jets, positive⟩, comp⟩ := source γ
  obtain ⟨M', meas, bounded, unchanged, _, smooth', jets'⟩ :=
    exists_bounded_measurable_signedCapEndpoint_profiles hR hb hA M smooth jets
  refine ⟨⟨M', A, meas, bounded, smooth', jets', ?_⟩, comp⟩
  intro i p h₁ h₂ h₃ hρ
  exact (positive i p h₁ h₂ h₃ hρ).trans (unchanged i _ _ _ hρ.1.ne').symm

end Burnett.A05

#print axioms Burnett.A05.exists_bounded_measurable_signedCapEndpoint_profiles
#print axioms Burnett.A05.analyticNearCapBudget_of_signed_profiles
