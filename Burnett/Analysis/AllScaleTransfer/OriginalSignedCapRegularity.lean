import Burnett.Analysis.AllScaleTransfer.OriginalCapRegularityGeometry

set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Filter Metric Set
open Burnett.A02.FrequencySplit Burnett.A05.BoxFourier
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped BigOperators ContDiff Topology

open private lowChartPoint lowChartPoint_continuousAt lowRatio_continuousAt lowBranchCycle lowBranchCycle_signed
  lowBranchCycle_continuous lowBranchCycle_symbol comparable_local_box_data radianFourBranchSymbol_scale_of_eq
  from Burnett.Analysis.AllScaleTransfer.OriginalBranchRegularity

private theorem paired_signed (a : E ≃L[ℝ] E) {p : Joint} (hp : p ∈ nonzeroSignedTriads) :
    pairedFrequencyEquiv a p ∈ nonzeroSignedTriads := by
  have nz {v : E} (hv : v ≠ 0) : a v ≠ 0 := fun h => hv (a.injective (h.trans a.map_zero.symm))
  refine ⟨nz hp.1,nz hp.2.1,?_⟩
  change -(a p.1+a p.2) ≠ 0
  rw [← a.map_add, ← a.map_neg]
  exact nz hp.2.2

private theorem pair_inverse (a : E ≃L[ℝ] E) (p : Joint) :
    pairedFrequencyEquiv a (pairedFrequencyEquiv a.symm p) = p :=
  Prod.ext (a.apply_symm_apply p.1) (a.apply_symm_apply p.2)

private theorem pair_smul (a : E ≃L[ℝ] E) (t : ℝ) (p : Joint) :
    pairedFrequencyEquiv a (t • p) = t • pairedFrequencyEquiv a p :=
  (pairedFrequencyEquiv a).map_smul t p

private def sameCapSlots (K : Set E) (p : Joint) : Prop := p.1 ∈ K ∧ p.2 ∈ K ∧ -(p.1+p.2) ∈ K

private theorem sameCapSlots_cycle {K : Set E} {p : Joint} (hp : sameCapSlots K p) (i : Fin 3) :
    sameCapSlots K (lowBranchCycle i p) := by
  have h₁ : -(p.2 + -(p.1+p.2)) = p.1 := by abel
  have h₂ : -(-(p.1+p.2) + p.1) = p.2 := by abel
  fin_cases i
  · exact hp
  · refine ⟨hp.2.1,hp.2.2,?_⟩
    change -(p.2 + -(p.1+p.2)) ∈ K
    rw [h₁]
    exact hp.1
  · refine ⟨hp.2.2,hp.1,?_⟩
    change -(-(p.1+p.2) + p.1) ∈ K
    rw [h₂]
    exact hp.2.1

private theorem sameCapSlots_of_pair {K : Set E} {p : Joint} (a : E ≃L[ℝ] E)
    (hp : sameCapSlots K (pairedFrequencyEquiv a p)) :
    a p.1 ∈ K ∧ a p.2 ∈ K ∧ a (-(p.1+p.2)) ∈ K := by
  refine ⟨hp.1,hp.2.1,?_⟩
  rw [a.map_neg,a.map_add]
  exact hp.2.2

private theorem signedProfile_at_positive_ratio (M : E → E → ℝ → ℂ) {R b A : ℝ}
    (smooth : ∀ s, ContDiffOn ℝ 100 (signedEndpointProfile M s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b))
    (jets : ∀ s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A)
    {q : Joint} (hq : q ∈ nonzeroSignedTriads) {ρ : ℝ} (hρ : ρ ∈ Ioo (0 : ℝ) b)
    (h₁ : (endpointDirection q.1) 0 ≠ 0 ∧ endpointTail (endpointDirection q.1) ∈ ball (0 : EndpointAngle) R)
    (h₂ : (endpointDirection q.2) 0 ≠ 0 ∧ endpointTail (endpointDirection q.2) ∈ ball (0 : EndpointAngle) R) :
    ContinuousAt (fun z : Joint × ℝ => M (endpointDirection z.1.1) (endpointDirection z.1.2) z.2) (q,ρ) ∧
      ‖M (endpointDirection q.1) (endpointDirection q.2) ρ‖ ≤ A := by
  have chooseSign (x : E) (hx : x 0 ≠ 0) : ∃ s : Bool, 0 < signedAxis s x := by
    rcases lt_or_gt_of_ne hx with h | h
    · exact ⟨false,neg_pos.mpr h⟩
    · exact ⟨true,h⟩
  obtain ⟨s,hs⟩ := chooseSign _ h₁.1
  obtain ⟨t,ht⟩ := chooseSign _ h₂.1
  let φ (z : Joint × ℝ) : LowRatio.Point :=
    ((endpointTail (endpointDirection z.1.1),endpointTail (endpointDirection z.1.2)),z.2)
  let U := capCorrectionAngles R ×ˢ Ico (0 : ℝ) b
  have hU : φ (q,ρ) ∈ U := ⟨⟨h₁.2,h₂.2⟩,hρ.1.le,hρ.2⟩
  have hDir : ContinuousAt (lowChartPoint ∘ (Prod.fst : Joint × ℝ → Joint)) (q,ρ) :=
    (lowChartPoint_continuousAt hq).comp continuous_fst.continuousAt
  have hDir₁ : ContinuousAt (fun z : Joint × ℝ => endpointDirection z.1.1) (q,ρ) :=
    continuous_fst.continuousAt.comp hDir
  have hDir₂ : ContinuousAt (fun z : Joint × ℝ => endpointDirection z.1.2) (q,ρ) :=
    continuous_snd.continuousAt.comp hDir
  have hφ : ContinuousAt φ (q,ρ) :=
    ((endpointTail.continuous.continuousAt.comp hDir₁).prodMk
      (endpointTail.continuous.continuousAt.comp hDir₂)).prodMk continuous_snd.continuousAt
  have hOpen : IsOpen (capCorrectionAngles R ×ˢ Ioo (0 : ℝ) b) :=
    (isOpen_ball.prod isOpen_ball).prod isOpen_Ioo
  have hφU : ∀ᶠ z in 𝓝 (q,ρ), φ z ∈ U :=
    (hφ.eventually_mem (hOpen.mem_nhds (show φ (q,ρ) ∈ capCorrectionAngles R ×ˢ Ioo (0 : ℝ) b
      from ⟨⟨h₁.2,h₂.2⟩,hρ⟩))).mono fun _ hz => ⟨hz.1,hz.2.1.le,hz.2.2⟩
  have axis (sig : Bool) : Continuous (signedAxis sig : E → ℝ) := by
    have head : Continuous (fun x : E => x 0) := frequencyCoordinates.continuous.fst
    cases sig
    · exact head.neg
    · exact head
  have pos₁ := ((axis s).continuousAt.comp hDir₁).eventually_mem (isOpen_Ioi.mem_nhds hs)
  have pos₂ := ((axis t).continuousAt.comp hDir₂).eventually_mem (isOpen_Ioi.mem_nhds ht)
  have eq {z : Joint × ℝ} (hz : z.1 ∈ nonzeroSignedTriads)
      (hpos₁ : 0 < signedAxis s (endpointDirection z.1.1))
      (hpos₂ : 0 < signedAxis t (endpointDirection z.1.2)) :
      M (endpointDirection z.1.1) (endpointDirection z.1.2) z.2 = signedEndpointProfile M (s,t) (φ z) := by
    unfold signedEndpointProfile
    rw [show (φ z).1.1 = endpointTail (endpointDirection z.1.1) from rfl,
      show (φ z).1.2 = endpointTail (endpointDirection z.1.2) from rfl,
      signedChartLift_endpointTail s (endpointDirection_mem_sphere hz.1) hpos₁,
      signedChartLift_endpointTail t (endpointDirection_mem_sphere hz.2.1) hpos₂]
  have cont : ContinuousAt (signedEndpointProfile M (s,t) ∘ φ) (q,ρ) :=
    ((smooth (s,t)).continuousOn _ hU).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hφ.tendsto,hφU⟩)
  refine ⟨cont.congr_of_eventuallyEq ?_,?_⟩
  · filter_upwards [continuous_fst.continuousAt.eventually_mem (isOpen_nonzeroSignedTriads.mem_nhds hq),pos₁,pos₂]
      with z hz ha hb
    exact eq hz ha hb
  · rw [eq (z := (q,ρ)) hq hs ht]
    simpa only [norm_iteratedFDerivWithin_zero] using jets (s,t) 0 (by decide) _ hU

private theorem cap_lowBranch_local (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    {κ b R A : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b)
    (a : E ≃L[ℝ] E) (K : Set E) (μ : Joint → ℂ) (i : Fin 3) (M : E → E → ℝ → ℂ)
    (smooth : ∀ s, ContDiffOn ℝ 100 (signedEndpointProfile M s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b))
    (jets : ∀ s n, n ≤ 100 → ∀ z ∈ capCorrectionAngles R ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (signedEndpointProfile M s) (capCorrectionAngles R ×ˢ Ico (0 : ℝ) b) z‖ ≤ A)
    (formula : ∀ z : Joint, a z.1 ∈ K → a z.2 ∈ K → a (-(z.1+z.2)) ∈ K →
      ‖a z.1‖/‖a z.2‖ ∈ Ioo (0 : ℝ) b →
      radianFourBranchSymbol ϑ κ (radianLowSlotView μ i) 0 (pairedFrequencyEquiv a z) =
        M (endpointDirection z.1) (endpointDirection z.2) (‖a z.1‖/‖a z.2‖))
    (angle : ∀ z : E, z ≠ 0 → a z ∈ K → (endpointDirection z) 0 ≠ 0 ∧
      endpointTail (endpointDirection z) ∈ ball (0 : EndpointAngle) R)
    {p : Joint} (hp : p ∈ nonzeroSignedTriads) (near : ∀ᶠ z in 𝓝 p, sameCapSlots K z)
    (active : radianFourBranchWeight ϑ κ i.castSucc p ≠ 0) :
    ContinuousAt (radianFourBranchSymbol ϑ κ μ i.castSucc) p ∧
      ‖radianFourBranchSymbol ϑ κ μ i.castSucc p‖ ≤ A := by
  let x : Joint → Joint := pairedFrequencyEquiv a.symm ∘ lowBranchCycle i
  let r (z : Joint) := ‖(lowBranchCycle i z).1‖/‖(lowBranchCycle i z).2‖
  have eqX (z : Joint) : pairedFrequencyEquiv a (x z) = lowBranchCycle i z := pair_inverse a _
  have eqR (z : Joint) : ‖a (x z).1‖/‖a (x z).2‖ = r z := by
    have h₁ := congrArg Prod.fst (eqX z)
    have h₂ := congrArg Prod.snd (eqX z)
    change ‖(pairedFrequencyEquiv a (x z)).1‖/‖(pairedFrequencyEquiv a (x z)).2‖ = r z
    rw [h₁,h₂]
  have hx : x p ∈ nonzeroSignedTriads := paired_signed a.symm (lowBranchCycle_signed i p hp)
  have rc : ContinuousAt r p := (lowRatio_continuousAt (lowBranchCycle_signed i p hp)).comp
    (lowBranchCycle_continuous i).continuousAt
  have active' : lowSlotWeight ϑ κ (lowBranchCycle i p).1 (lowBranchCycle i p).2
      (-((lowBranchCycle i p).1+(lowBranchCycle i p).2)) ≠ 0 := by
    have eq := lowBranchCycle_symbol ϑ κ (fun _ => (1 : ℂ)) i p
    have viewOne (z : Joint) : radianLowSlotView (fun _ => (1 : ℂ)) i z = 1 := by
      fin_cases i <;> rfl
    have eqW : (radianFourBranchWeight ϑ κ 0 (lowBranchCycle i p) : ℂ) =
        (radianFourBranchWeight ϑ κ i.castSucc p : ℂ) := by
      simpa only [radianFourBranchSymbol,viewOne,mul_one] using eq
    change radianFourBranchWeight ϑ κ 0 (lowBranchCycle i p) ≠ 0
    intro h
    rw [h, Complex.ofReal_zero] at eqW
    exact active (Complex.ofReal_eq_zero.mp eqW.symm)
  have hu := lowBranchCycle_signed i p hp
  have hr : r p ∈ Ioo (0 : ℝ) b := ⟨div_pos (norm_pos_iff.mpr hu.1) (norm_pos_iff.mpr hu.2.1),
    ((div_lt_iff₀ (norm_pos_iff.mpr hu.2.1)).mpr (lowSlotWeight_nonzero_ratio_margin hCut hκ hκsmall
      (add_neg_cancel _) hu.2.1 active')).trans hb⟩
  have slots {z : Joint} (hz : sameCapSlots K z) :
      a (x z).1 ∈ K ∧ a (x z).2 ∈ K ∧ a (-((x z).1+(x z).2)) ∈ K :=
    sameCapSlots_of_pair a ((eqX z).symm ▸ sameCapSlots_cycle hz i)
  have hKp : sameCapSlots K p := mem_of_mem_nhds (s := {z : Joint | sameCapSlots K z}) near
  have hk := slots hKp
  obtain ⟨cont,mag⟩ := signedProfile_at_positive_ratio M smooth jets hx hr
    (angle _ hx.1 hk.1) (angle _ hx.2.1 hk.2.1)
  have eq {z : Joint} (hz : sameCapSlots K z) (hzr : r z ∈ Ioo (0 : ℝ) b) :
      radianFourBranchSymbol ϑ κ μ i.castSucc z = M (endpointDirection (x z).1) (endpointDirection (x z).2) (r z) := by
    have ks := slots hz
    have same := formula (x z) ks.1 ks.2.1 ks.2.2 (by rwa [eqR])
    rw [eqX,lowBranchCycle_symbol,eqR] at same
    exact same
  have hInput : ContinuousAt (fun z : Joint => (x z,r z)) p :=
    ((pairedFrequencyEquiv a.symm).continuous.comp (lowBranchCycle_continuous i)).continuousAt.prodMk rc
  have cont' := ContinuousAt.comp (f := fun z : Joint => (x z,r z)) (x := p) cont hInput
  refine ⟨cont'.congr_of_eventuallyEq ?_,?_⟩
  · filter_upwards [near,rc.eventually_mem (isOpen_Ioo.mem_nhds hr)] with z hz hzr
    exact eq hz hzr
  · rw [eq hKp hr]
    exact mag

private theorem cap_compareBranch_local (ϑ : ℝ → ℝ) (κ : ℝ) (a : E ≃L[ℝ] E) (μ : Joint → ℂ)
    {p : Joint} (hp : p ∈ nonzeroSignedTriads) {A : ℝ} {N : ℕ}
    (hom : ∀ t : ℝ, 0 < t → ∀ z ∈ nonzeroSignedTriads, μ (t • z) = μ z)
    (boxes : AnalyticNearComparableBudget N A (radianFourBranchSymbol ϑ κ μ 3 ∘ pairedFrequencyEquiv a))
    {j k : ℤ} (hk : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ))
    (hFirst : integerRadialWindow (j+k) (a.symm p.1) ≠ 0) (hSecond : integerRadialWindow j (a.symm p.2) ≠ 0) :
    ContinuousAt (radianFourBranchSymbol ϑ κ μ 3) p ∧ ‖radianFourBranchSymbol ϑ κ μ 3 p‖ ≤ A := by
  let f := radianFourBranchSymbol ϑ κ μ 3 ∘ pairedFrequencyEquiv a
  have fh (t : ℝ) (ht : 0 < t) (z : Joint) (hz : z ∈ nonzeroSignedTriads) : f (t • z) = f z := by
    unfold f
    simp only [Function.comp_apply, pair_smul]
    exact radianFourBranchSymbol_scale_of_eq ϑ κ μ 3 _ t ht (hom t ht _ (paired_signed a hz))
  -- The complementary branch of the zero cutoff is the input itself.
  have same : radianFourBranchSymbol (fun _ => 0) 0 f 3 = f := by
    funext z
    change ((comparableSlotWeight (fun _ => 0) 0 z.1 z.2 (-(z.1+z.2)) : ℝ) : ℂ) * f z = f z
    simp [comparableSlotWeight,lowSlotWeight]
  have boxes' : AnalyticNearComparableBudget N A (radianFourBranchSymbol (fun _ => 0) 0 f 3) := by
    rw [same]
    exact boxes
  have localData := comparable_local_box_data (fun _ => 0) 0 f fh boxes' hk
    (paired_signed a.symm hp) hFirst hSecond
  rw [same] at localData
  have eq : f ∘ pairedFrequencyEquiv a.symm = radianFourBranchSymbol ϑ κ μ 3 := by
    funext z
    simp only [f,Function.comp_apply,pair_inverse]
  rw [← eq]
  exact ⟨localData.1.comp (pairedFrequencyEquiv a.symm).continuous.continuousAt,localData.2⟩

/-- Actual signed cap profiles on the uniformly chosen domains recover
regularity of the original near symbol on the nonzero signed triads. -/
theorem exists_analyticNearOriginalSymbol_of_signedCapProfiles (ϑ : ℝ → ℝ) (hϑ : Continuous ϑ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (B tube outer enlarged : ℝ) (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    {κ b : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b) :
    ∃ (R : ℝ) (N : ℕ), 0 < R ∧ R < 1 ∧
      ∀ {metric : Form} {δ inner D : ℝ} (hδ : 0 < δ), 4*B*(5*δ) ≤ 1 → inner ≤ outer →
        ∀ (S : SmoothThinConeCaps metric δ (tube*δ^2) inner outer enlarged D)
        (chart : ∀ γ : ↑S.centers, NullCapChart metric γ),
        (∀ γ, ‖(chart γ).toFrequency.symm.toContinuousLinearMap‖ ≤ B) →
        ∀ (m : Joint → ℂ),
        (∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p) →
        AnalyticNearAdjacentSupport metric δ (tube*δ^2) inner m → ∀ A ≥ 0,
        AnalyticNearSignedCapProfiles ϑ κ b R A N hδ.ne' S chart m → AnalyticNearOriginalSymbol m := by
  obtain ⟨R,N,hR,hR₁,covers⟩ := exists_analyticNearCap_atlas_coverage hCut hFlat B tube outer enlarged
    hB hTube hOut hOE hκ hκsmall
  refine ⟨R,N,hR,hR₁,?_⟩
  intro metric δ inner D hδ hSmall hIO S chart hI m hom adj A hA profiles
  let η := tube*δ^2
  have hη : 0 ≤ η := mul_nonneg hTube.le (sq_nonneg δ)
  let μ (γ : ↑S.centers) : Joint → ℂ := ((δ^2)⁻¹ • capLocalizedNearSymbol S m γ : Joint → ℂ)
  have localSymbol (γ : ↑S.centers) : AnalyticNearOriginalSymbol (μ γ) := by
    have homμ (t : ℝ) (ht : 0 < t) (p : Joint) (hp : p ∈ nonzeroSignedTriads) : μ γ (t • p) = μ γ p := by
      simp only [μ,Pi.smul_apply,capLocalizedNearSymbol,Prod.smul_fst,hom t ht p hp,
        (S.degree_zero γ γ.property).1 t ht.ne' p.1]
    let a := capFrequencyEquiv (chart γ) hδ.ne'
    let K := tsupport (enlargedCapMultiplier metric δ η outer enlarged γ)
    obtain ⟨angle,compCover⟩ := covers metric γ (chart γ) (S.centers_null γ.property).1 (hI γ) δ hδ hSmall
    obtain ⟨⟨M,smooth,jets,hMatch⟩,boxes⟩ := profiles γ
    apply analyticNearOriginalSymbol_of_localFourBranches ϑ hϑ hκ (μ γ) hA homμ
    intro i p hp active
    by_cases hs : p ∈ tsupport (capLocalizedNearSymbol S m γ)
    · have near : ∀ᶠ z in 𝓝 p, sameCapSlots K z :=
        eventually_enlargedCap_of_mem_tsupport_capLocalizedNearSymbol S hη hIO m adj γ hp hs
      fin_cases i
      · exact cap_lowBranch_local ϑ hCut hκ hκsmall hb a K (μ γ) 0 (M 0)
          (smooth 0) (jets 0) (hMatch 0) angle hp near active
      · exact cap_lowBranch_local ϑ hCut hκ hκsmall hb a K (μ γ) 1 (M 1)
          (smooth 1) (jets 1) (hMatch 1) angle hp near active
      · exact cap_lowBranch_local ϑ hCut hκ hκsmall hb a K (μ γ) 2 (M 2)
          (smooth 2) (jets 2) (hMatch 2) angle hp near active
      · have hKp : sameCapSlots K p := mem_of_mem_nhds (s := {z : Joint | sameCapSlots K z}) near
        have hpairs := sameCapSlots_of_pair a ((pair_inverse a p).symm ▸ hKp)
        have active' : comparableSlotWeight ϑ κ (a (a.symm p.1)) (a (a.symm p.2))
            (a (-(a.symm p.1+a.symm p.2))) ≠ 0 := by
          change comparableSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) ≠ 0 at active
          simpa only [a.map_neg,a.map_add,a.apply_symm_apply] using active
        obtain ⟨j,k,hk,first,second⟩ := compCover (pairedFrequencyEquiv a.symm p)
          (paired_signed a.symm hp) hpairs.1 hpairs.2.1 hpairs.2.2 active'
        exact cap_compareBranch_local ϑ κ a (μ γ) hp homμ boxes hk first second
    · have ev : capLocalizedNearSymbol S m γ =ᶠ[𝓝 p] 0 := notMem_tsupport_iff_eventuallyEq.mp hs
      have ez : radianFourBranchSymbol ϑ κ (μ γ) i =ᶠ[𝓝 p] 0 := by
        filter_upwards [ev] with z hz
        change capLocalizedNearSymbol S m γ z = 0 at hz
        simp only [radianFourBranchSymbol,μ,Pi.smul_apply,hz,smul_zero,mul_zero,Pi.zero_apply]
      refine ⟨continuousAt_const.congr_of_eventuallyEq ez,?_⟩
      have atP : radianFourBranchSymbol ϑ κ (μ γ) i p = 0 :=
        mem_of_mem_nhds (s := {z : Joint | radianFourBranchSymbol ϑ κ (μ γ) i z = 0}) ez
      rw [atP,norm_zero]
      exact hA
  have recover (γ : ↑S.centers) (p : Joint) : δ^2 • μ γ p = capLocalizedNearSymbol S m γ p := by
    simp only [μ,Pi.smul_apply,smul_smul,mul_inv_cancel₀ (pow_ne_zero 2 hδ.ne'),one_smul]
  have orig (p : Joint) (hp : p ∈ nonzeroSignedTriads) : m p = ∑ γ, δ^2 • μ γ p := by
    simp_rw [recover]
    exact (capLocalizedNearSymbol_sum_on_nonzeroSignedTriads S m adj hp).symm
  choose W hW ub using fun γ => (localSymbol γ).bounded
  refine ⟨?_,⟨∑ γ, δ^2*W γ, Finset.sum_nonneg (fun γ _ => mul_nonneg (sq_nonneg δ) (hW γ)),?_⟩,hom⟩
  · exact (continuousOn_finset_sum _ (fun γ _ => continuousOn_const.smul (localSymbol γ).continuous)).congr orig
  · intro p hp
    rw [orig p hp]
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro γ _
    rw [norm_smul, Real.norm_of_nonneg (sq_nonneg δ)]
    exact mul_le_mul_of_nonneg_left (ub γ p hp) (sq_nonneg δ)

end Burnett.A05

#print axioms Burnett.A05.exists_analyticNearOriginalSymbol_of_signedCapProfiles
