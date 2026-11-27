import Burnett.Analysis.AllScaleTransfer.OriginalAnalyticNear

set_option autoImplicit false
set_option maxRecDepth 9000
set_option maxHeartbeats 15000000

noncomputable section

namespace Burnett.A05

open Filter Metric Set
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier Burnett.C02
open Burnett.Analysis CapFourier ProjectiveNullCaps
open scoped BigOperators ContDiff Topology

private theorem radianFourBranchSymbol_scale_of_eq (ϑ : ℝ → ℝ) (κ : ℝ)
    (m : Joint → ℂ) (i : Fin 4) (p : Joint) (t : ℝ) (ht : 0 < t) (hm : m (t • p) = m p) :
    radianFourBranchSymbol ϑ κ m i (t • p) = radianFourBranchSymbol ϑ κ m i p := by
  have hw : (radianFourBranchWeight ϑ κ i (t • p) : ℂ) =
      (radianFourBranchWeight ϑ κ i p : ℂ) := by
    simpa only [radianFourBranchSymbol, mul_one] using
      radianFourBranchSymbol_homogeneous ϑ κ (fun _ => (1 : ℂ)) (fun _ _ _ => rfl) i t ht p
  simp only [radianFourBranchSymbol, hw, hm]

private theorem radianFourBranchWeight_continuousAt_of_signed (ϑ : ℝ → ℝ)
    (hϑ : Continuous ϑ) {κ : ℝ} (hκ : 0 < κ) {p : Joint} (hp : p ∈ nonzeroSignedTriads)
    (i : Fin 4) : ContinuousAt (radianFourBranchWeight ϑ κ i) p := by
  have low {f g h : Joint → E} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h)
      (hg0 : g p ≠ 0) : ContinuousAt (fun z => lowSlotWeight ϑ κ (f z) (g z) (h z)) p := by
    have hd : 0 < κ^2 * (‖g p‖^2 + ‖h p‖^2) :=
      mul_pos (pow_pos hκ 2) (add_pos_of_pos_of_nonneg (pow_pos (norm_pos_iff.mpr hg0) 2) (sq_nonneg _))
    unfold lowSlotWeight
    exact hϑ.continuousAt.comp ((hf.norm.continuousAt.pow 2).div
      (continuousAt_const.mul ((hg.norm.continuousAt.pow 2).add (hh.norm.continuousAt.pow 2))) hd.ne')
  have third : Continuous (fun z : Joint => -(z.1+z.2)) := (continuous_fst.add continuous_snd).neg
  have first := low continuous_fst continuous_snd third hp.2.1
  have second := low continuous_snd third continuous_fst hp.2.2
  have last := low third continuous_fst continuous_snd hp.1
  fin_cases i
  · exact first
  · exact second
  · exact last
  · exact (((continuousAt_const.sub first).sub second).sub last)

/-- The literal four branches recover continuity and a global bound for the
symbol on the nonzero signed triads from local data on their active sets. -/
theorem analyticNearOriginalSymbol_of_localFourBranches (ϑ : ℝ → ℝ) (hϑ : Continuous ϑ)
    {κ : ℝ} (hκ : 0 < κ) (m : Joint → ℂ) {A : ℝ} (hA : 0 ≤ A)
    (hom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p)
    (localData : ∀ (i : Fin 4) (p : Joint), p ∈ nonzeroSignedTriads →
      radianFourBranchWeight ϑ κ i p ≠ 0 →
      ContinuousAt (radianFourBranchSymbol ϑ κ m i) p ∧ ‖radianFourBranchSymbol ϑ κ m i p‖ ≤ A) :
    AnalyticNearOriginalSymbol m := by
  refine ⟨?_, ⟨4*A, by positivity, ?_⟩, hom⟩
  · intro p hp
    obtain ⟨i, hi⟩ : ∃ i : Fin 4, radianFourBranchWeight ϑ κ i p ≠ 0 := by
      by_contra! zero
      have h := radianFourBranchSymbol_sum ϑ κ (fun _ => (1 : ℂ)) p
      simp only [radianFourBranchSymbol, zero, Complex.ofReal_zero, zero_mul, Finset.sum_const_zero] at h
      exact zero_ne_one h
    have hW := radianFourBranchWeight_continuousAt_of_signed ϑ hϑ hκ hp i
    have quot := (localData i p hp hi).1.div
      (Complex.continuous_ofReal.continuousAt.comp hW) (Complex.ofReal_ne_zero.mpr hi)
    apply ContinuousAt.continuousWithinAt (quot.congr_of_eventuallyEq ?_)
    filter_upwards [hW.eventually_ne hi] with z hz
    change m z = ((radianFourBranchWeight ϑ κ i z : ℂ) * m z) / (radianFourBranchWeight ϑ κ i z : ℂ)
    rw [mul_comm, mul_div_cancel_right₀ _ (Complex.ofReal_ne_zero.mpr hz)]
  · intro p hp
    calc
      ‖m p‖ = ‖∑ i : Fin 4, radianFourBranchSymbol ϑ κ m i p‖ := by
        rw [radianFourBranchSymbol_sum]
      _ ≤ ∑ i : Fin 4, ‖radianFourBranchSymbol ϑ κ m i p‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin 4, A := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : radianFourBranchWeight ϑ κ i p = 0
        · simpa only [radianFourBranchSymbol, hi, Complex.ofReal_zero, zero_mul, norm_zero] using hA
        · exact (localData i p hp hi).2
      _ = 4*A := by simp [nsmul_eq_mul]

private abbrev lowChartPoint (p : Joint) : Joint := (endpointDirection p.1, endpointDirection p.2)

private theorem lowChartPoint_continuousAt {p : Joint} (hp : p ∈ nonzeroSignedTriads) :
    ContinuousAt lowChartPoint p := by
  have unitAt {x : E} (hx : x ≠ 0) : ContinuousAt endpointDirection x :=
    (endpointDirection_contDiffOn.continuousOn x hx).continuousAt
      ((isOpen_ne_fun continuous_id continuous_const).mem_nhds hx)
  exact ((unitAt hp.1).comp continuous_fst.continuousAt).prodMk
    ((unitAt hp.2.1).comp continuous_snd.continuousAt)

private theorem lowRatio_continuousAt {p : Joint} (hp : p ∈ nonzeroSignedTriads) :
    ContinuousAt (fun z : Joint => ‖z.1‖/‖z.2‖) p :=
  continuous_fst.norm.continuousAt.div continuous_snd.norm.continuousAt (norm_ne_zero_iff.mpr hp.2.1)

private theorem lowChartPoint_unit {p : Joint} (hp : p ∈ nonzeroSignedTriads) :
    ‖(lowChartPoint p).1‖ = 1 ∧ ‖(lowChartPoint p).2‖ = 1 :=
  ⟨mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp.1),
    mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp.2.1)⟩

private theorem firstLow_local_atlas_data {b A : ℝ} (f : Joint → ℂ)
    (hom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, f (t • p) = f p)
    (M : WardPairChart → LowRatio.Point → ℂ)
    (smooth : ∀ i, ContDiffOn ℝ 100 (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b))
    (jets : ∀ i n, n ≤ 100 → ∀ z ∈ wardPairChartDomain i ×ˢ Ico (0 : ℝ) b,
      ‖iteratedFDerivWithin ℝ n (M i) (wardPairChartDomain i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A)
    (formula : ∀ i pq, pq ∈ wardPairChartAnnulus i → ∀ t : ℝ, 0 < t →
      let ρ := t*(‖pq.1‖/‖pq.2‖)
      ρ ∈ Ioo (0 : ℝ) b → f (t • pq.1,pq.2) = M i (wardPairChartAngles i pq,ρ))
    {p : Joint} (hp : p ∈ nonzeroSignedTriads) (hρ : ‖p.1‖/‖p.2‖ ∈ Ioo (0 : ℝ) b) :
    ContinuousAt f p ∧ ‖f p‖ ≤ A := by
  have hAnn : lowChartPoint p ∈ radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2 := by
    have hu := lowChartPoint_unit hp
    change (1/2 ≤ ‖(lowChartPoint p).1‖ ∧ ‖(lowChartPoint p).1‖ ≤ 2) ∧
      (1/2 ≤ ‖(lowChartPoint p).2‖ ∧ ‖(lowChartPoint p).2‖ ≤ 2)
    norm_num [hu.1, hu.2]
  obtain ⟨i, hi⟩ := mem_iUnion.mp (wardPairChartAnnulus_covers hAnn)
  let φ (z : Joint) : LowRatio.Point := (wardPairChartAngles i (lowChartPoint z),‖z.1‖/‖z.2‖)
  let U := wardPairChartDomain i ×ˢ Ico (0 : ℝ) b
  have hφ : ContinuousAt φ p :=
    ((((wardPairChartAngles_smooth i).continuousOn _ hi).continuousAt
      ((wardPairChartAnnulus_open i).mem_nhds hi)).comp (lowChartPoint_continuousAt hp)).prodMk
      (lowRatio_continuousAt hp)
  have hφU : φ p ∈ U := ⟨wardPairChartAngles_mapsTo i hi,hρ.1.le,hρ.2⟩
  have same {z : Joint} (hz : z ∈ nonzeroSignedTriads) (hzi : lowChartPoint z ∈ wardPairChartAnnulus i)
      (hzρ : ‖z.1‖/‖z.2‖ ∈ Ioo (0 : ℝ) b) : f z = M i (φ z) := by
    have hu := lowChartPoint_unit hz
    have hMatch := formula i (lowChartPoint z) hzi _ hzρ.1
    simp only [hu.1, hu.2, div_one, mul_one] at hMatch
    have hscale : ((‖z.1‖/‖z.2‖) • (lowChartPoint z).1,(lowChartPoint z).2) = ‖z.2‖⁻¹ • z := by
      apply Prod.ext
      · change (‖z.1‖/‖z.2‖) • (‖z.1‖⁻¹ • z.1) = ‖z.2‖⁻¹ • z.1
        rw [smul_smul,div_eq_mul_inv,mul_comm ‖z.1‖,mul_assoc,
          mul_inv_cancel₀ (norm_ne_zero_iff.mpr hz.1), mul_one]
      · rfl
    rw [← hom ‖z.2‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hz.2.1)) z hz, ← hscale]
    exact hMatch hzρ
  have arc := (lowChartPoint_continuousAt hp).eventually_mem ((wardPairChartAnnulus_open i).mem_nhds hi)
  have ratio := (lowRatio_continuousAt hp).eventually_mem (isOpen_Ioo.mem_nhds hρ)
  have hNear : ∀ᶠ z in 𝓝 p, φ z ∈ U := by
    filter_upwards [arc,ratio] with z hzi hratio
    exact ⟨wardPairChartAngles_mapsTo i hzi,hratio.1.le,hratio.2⟩
  have cont : ContinuousAt (M i ∘ φ) p :=
    ((smooth i).continuousOn _ hφU).tendsto.comp (tendsto_nhdsWithin_iff.mpr ⟨hφ.tendsto,hNear⟩)
  refine ⟨cont.congr_of_eventuallyEq ?_,?_⟩
  · filter_upwards [isOpen_nonzeroSignedTriads.mem_nhds hp,arc,ratio] with z hz hzi hratio
    exact same hz hzi hratio
  · rw [same hp hi hρ]
    simpa only [norm_iteratedFDerivWithin_zero] using jets i 0 (by decide) _ hφU

private theorem radianCycle_signed (p : Joint) (hp : p ∈ nonzeroSignedTriads) :
    radianCycle p ∈ nonzeroSignedTriads ∧ radianCycle.symm p ∈ nonzeroSignedTriads := by
  have h₁ : -(p.2 + -(p.1 + p.2)) = p.1 := by abel
  have h₂ : -(-(p.1 + p.2) + p.1) = p.2 := by abel
  refine ⟨⟨hp.2.1,hp.2.2,?_⟩,⟨hp.2.2,hp.1,?_⟩⟩
  · change -(p.2 + -(p.1+p.2)) ≠ 0
    rw [h₁]
    exact hp.1
  · change -(-(p.1+p.2) + p.1) ≠ 0
    rw [h₂]
    exact hp.2.1

private theorem view_homogeneous (m : Joint → ℂ)
    (hom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p)
    (i : Fin 3) (t : ℝ) (ht : 0 < t) (p : Joint) (hp : p ∈ nonzeroSignedTriads) :
    radianLowSlotView m i (t • p) = radianLowSlotView m i p := by
  have cycles := radianCycle_signed p hp
  fin_cases i
  · exact hom t ht p hp
  · change m (-(t • p.1+t • p.2),t • p.1) = m (radianCycle.symm p)
    rw [← smul_add,← smul_neg]
    exact hom t ht (radianCycle.symm p) cycles.2
  · change m (t • p.2,-(t • p.1+t • p.2)) = m (radianCycle p)
    rw [← smul_add,← smul_neg]
    exact hom t ht (radianCycle p) cycles.1

private def lowBranchCycle (i : Fin 3) : Joint → Joint := ![id,radianCycle,radianCycle.symm] i

private theorem lowBranchCycle_signed (i : Fin 3) (p : Joint) (hp : p ∈ nonzeroSignedTriads) :
    lowBranchCycle i p ∈ nonzeroSignedTriads := by
  fin_cases i
  · exact hp
  · exact (radianCycle_signed p hp).1
  · exact (radianCycle_signed p hp).2

private theorem lowBranchCycle_continuous (i : Fin 3) : Continuous (lowBranchCycle i) := by
  fin_cases i
  · exact continuous_id
  · exact continuous_snd.prodMk (continuous_fst.add continuous_snd).neg
  · exact (continuous_fst.add continuous_snd).neg.prodMk continuous_fst

private theorem lowBranchCycle_symbol (ϑ : ℝ → ℝ) (κ : ℝ) (m : Joint → ℂ) (i : Fin 3) (p : Joint) :
    radianFourBranchSymbol ϑ κ (radianLowSlotView m i) 0 (lowBranchCycle i p) =
      radianFourBranchSymbol ϑ κ m i.castSucc p := by
  have h₁ : -(p.2 + -(p.1 + p.2)) = p.1 := by abel
  have h₂ : -(-(p.1 + p.2) + p.1) = p.2 := by abel
  fin_cases i
  · rfl
  · change ((lowSlotWeight ϑ κ p.2 (-(p.1+p.2)) (-(p.2 + -(p.1+p.2))) : ℝ) : ℂ) *
      m (radianCycle.symm (radianCycle p)) = _
    rw [h₁, MeasurableEquiv.symm_apply_apply]
    rfl
  · change ((lowSlotWeight ϑ κ (-(p.1+p.2)) p.1 (-(-(p.1+p.2) + p.1)) : ℝ) : ℂ) *
      m (radianCycle (radianCycle.symm p)) = _
    rw [h₂, MeasurableEquiv.apply_symm_apply]
    rfl

private theorem lowBranch_local_data (ϑ : ℝ → ℝ) (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    {κ b A : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) (hb : 7*κ/4 < b) (m : Joint → ℂ)
    (hom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p)
    (atlas : AnalyticNearPositiveAtlas ϑ κ b A m) (i : Fin 3) {p : Joint} (hp : p ∈ nonzeroSignedTriads)
    (active : radianFourBranchWeight ϑ κ i.castSucc p ≠ 0) :
    ContinuousAt (radianFourBranchSymbol ϑ κ m i.castSucc) p ∧
      ‖radianFourBranchSymbol ϑ κ m i.castSucc p‖ ≤ A := by
  let q := lowBranchCycle i p
  let f := radianFourBranchSymbol ϑ κ (radianLowSlotView m i) 0
  have hpq := lowBranchCycle_signed i p hp
  have wNonzero : lowSlotWeight ϑ κ q.1 q.2 (-(q.1+q.2)) ≠ 0 := by
    have h₁ : -(p.2 + -(p.1 + p.2)) = p.1 := by abel
    have h₂ : -(-(p.1 + p.2) + p.1) = p.2 := by abel
    fin_cases i
    · exact active
    · change lowSlotWeight ϑ κ p.2 (-(p.1+p.2)) (-(p.2 + -(p.1+p.2))) ≠ 0
      rw [h₁]
      exact active
    · change lowSlotWeight ϑ κ (-(p.1+p.2)) p.1 (-(-(p.1+p.2) + p.1)) ≠ 0
      rw [h₂]
      exact active
  have hρ : ‖q.1‖/‖q.2‖ ∈ Ioo (0 : ℝ) b := ⟨
    div_pos (norm_pos_iff.mpr hpq.1) (norm_pos_iff.mpr hpq.2.1),
    ((div_lt_iff₀ (norm_pos_iff.mpr hpq.2.1)).mpr
      (lowSlotWeight_nonzero_ratio_margin hCut hκ hκsmall (add_neg_cancel _) hpq.2.1 wNonzero)).trans hb⟩
  obtain ⟨M,hSmooth,hJets,hMatch⟩ := atlas i
  have out := firstLow_local_atlas_data f
    (fun t ht z hz => radianFourBranchSymbol_scale_of_eq ϑ κ _ 0 z t ht (view_homogeneous m hom i t ht z hz))
    M hSmooth hJets hMatch hpq hρ
  have eq : f ∘ lowBranchCycle i = radianFourBranchSymbol ϑ κ m i.castSucc :=
    funext (lowBranchCycle_symbol ϑ κ m i)
  rw [← eq]
  exact ⟨out.1.comp (lowBranchCycle_continuous i).continuousAt, out.2⟩

/-- Covers the active comparable branch by actual simultaneously nonzero
normalized annular windows, with a fixed interval of signed offsets. -/
def AnalyticNearComparableCoverage (ϑ : ℝ → ℝ) (κ : ℝ) (N : ℕ) : Prop :=
  ∀ p ∈ nonzeroSignedTriads, radianFourBranchWeight ϑ κ 3 p ≠ 0 →
    ∃ j k : ℤ, k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) ∧
      integerRadialWindow (j+k) p.1 ≠ 0 ∧ integerRadialWindow j p.2 ≠ 0

theorem exists_analyticNearComparableCoverage {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    {κ : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16) :
    ∃ N : ℕ, AnalyticNearComparableCoverage ϑ κ N := by
  classical
  obtain ⟨N, shifts⟩ := exists_comparable_integerRadialWindow_finiteShifts hCut hFlat κ 1 1
    hκ hκsmall zero_lt_one zero_lt_one
  refine ⟨N,?_⟩
  intro p hp active
  obtain ⟨j,hj⟩ : ∃ j : ℤ, integerRadialWindow j p.2 ≠ 0 := by
    by_contra! hZero
    have h := (integerRadialWindow_hasSum p.2).tsum_eq
    rw [if_neg hp.2.1] at h
    simp only [hZero,tsum_zero] at h
    exact zero_ne_one h
  change comparableSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2)) ≠ 0 at active
  have cover := (shifts (ContinuousLinearEquiv.refl ℝ E) p.1 p.2 j hj
    (by simpa only [ContinuousLinearEquiv.refl_apply] using active)
    (by simp) (by simp) (by simp)).2.1
  obtain ⟨k,hk,ha⟩ : ∃ k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), integerRadialWindow (j+k) p.1 ≠ 0 := by
    by_contra! hZero
    rw [Finset.sum_eq_zero hZero] at cover
    exact zero_ne_one cover
  exact ⟨j,k,hk,ha,hj⟩

private theorem comparable_local_box_data (ϑ : ℝ → ℝ) (κ : ℝ) (m : Joint → ℂ) {A : ℝ} {N : ℕ}
    (hom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p)
    (boxes : AnalyticNearComparableBudget N A (radianFourBranchSymbol ϑ κ m 3))
    {j k : ℤ} (hk : k ∈ Finset.Icc (-(N : ℤ)) (N : ℤ)) {p : Joint} (hp : p ∈ nonzeroSignedTriads)
    (hFirst : integerRadialWindow (j+k) p.1 ≠ 0) (hSecond : integerRadialWindow j p.2 ≠ 0) :
    ContinuousAt (radianFourBranchSymbol ϑ κ m 3) p ∧ ‖radianFourBranchSymbol ϑ κ m 3 p‖ ≤ A := by
  obtain ⟨G,hSmooth,hJets,hEq⟩ := boxes
  let normPair (z : Joint) : Joint := ((2 : ℝ)^(-(j+k)) • z.1, (2 : ℝ)^(-j) • z.2)
  let φ (z : Joint) : BoxSpace := boxToPair.symm (normPair z)
  have zcont : Continuous normPair :=
    (continuous_const.smul continuous_fst).prodMk (continuous_const.smul continuous_snd)
  have φcont : Continuous φ := boxToPair.symm.continuous.comp zcont
  have φeq (z : Joint) : φ z = joinedInputs (normPair z).1 (normPair z).2 := by
    apply boxToPair.injective
    rw [boxToPair_joined]
    exact boxToPair.apply_symm_apply (normPair z)
  have active₁ : endpointHighProfile (normPair p).1 ≠ 0 := by
    change endpointHighProfile ((2 : ℝ)^(-(j+k)) • p.1) ≠ 0
    rw [endpointHighProfile_eq_integerRadialWindow]
    exact_mod_cast hFirst
  have active₂ : endpointHighProfile (normPair p).2 ≠ 0 := by
    change endpointHighProfile ((2 : ℝ)^(-j) • p.2) ≠ 0
    rw [endpointHighProfile_eq_integerRadialWindow]
    exact_mod_cast hSecond
  have inBox : φ p ∈ ball (0 : BoxSpace) 5 := by
    rw [φeq]
    have h₁ := (endpointHighProfile_properties.2.2 _ active₁).2
    have h₂ := (endpointHighProfile_properties.2.2 _ active₂).2
    have sq := norm_joinedInputs_sq (normPair p).1 (normPair p).2
    apply mem_ball_zero_iff.mpr
    nlinarith [sq_nonneg (‖(normPair p).1‖-2), sq_nonneg (‖(normPair p).2‖-2),
      mul_nonneg (norm_nonneg (normPair p).1) (sub_nonneg.mpr h₁.le),
      mul_nonneg (norm_nonneg (normPair p).2) (sub_nonneg.mpr h₂.le),
      sq_nonneg (‖joinedInputs (normPair p).1 (normPair p).2‖-5)]
  have same {z : Joint} (hz : z ∈ nonzeroSignedTriads)
      (ha : endpointHighProfile (normPair z).1 ≠ 0) (hb : endpointHighProfile (normPair z).2 ≠ 0) :
      radianFourBranchSymbol ϑ κ m 3 z = G k (φ z) := by
    let w : Joint := ((2 : ℝ)^k • (normPair z).1,(normPair z).2)
    have hRecon : (2 : ℝ)^j • w = z := by
      have hTwo : (2 : ℝ) ≠ 0 := by norm_num
      apply Prod.ext
      · change (2 : ℝ)^j • ((2 : ℝ)^k • ((2 : ℝ)^(-(j+k)) • z.1)) = z.1
        rw [smul_smul,smul_smul,← zpow_add₀ hTwo,← zpow_add₀ hTwo,add_neg_cancel,zpow_zero,one_smul]
      · change (2 : ℝ)^j • ((2 : ℝ)^(-j) • z.2) = z.2
        rw [smul_smul,← zpow_add₀ hTwo,add_neg_cancel,zpow_zero,one_smul]
    have hw : w ∈ nonzeroSignedTriads := by
      rw [← hRecon] at hz
      refine ⟨fun h => hz.1 (by simp [h]), fun h => hz.2.1 (by simp [h]), ?_⟩
      intro h
      apply hz.2.2
      change -((2 : ℝ)^j • w.1 + (2 : ℝ)^j • w.2) = 0
      rw [← smul_add,← smul_neg,h,smul_zero]
    have hs := radianFourBranchSymbol_scale_of_eq ϑ κ m 3 w ((2 : ℝ)^j) (by positivity)
      (hom _ (by positivity) w hw)
    calc
      _ = radianFourBranchSymbol ϑ κ m 3 w := (congrArg _ hRecon).symm.trans hs
      _ = G k (φ z) := by
        rw [φeq]
        exact (hEq k hk (normPair z).1 (normPair z).2 ha hb).symm
  have cont : ContinuousAt (G k ∘ φ) p :=
    (((hSmooth k hk).continuousOn _ inBox).continuousAt (isOpen_ball.mem_nhds inBox)).comp φcont.continuousAt
  have firstAt : ContinuousAt (fun z => endpointHighProfile (normPair z).1) p :=
    (endpointHighProfile.continuous.comp (continuous_fst.comp zcont)).continuousAt
  have secondAt : ContinuousAt (fun z => endpointHighProfile (normPair z).2) p :=
    (endpointHighProfile.continuous.comp (continuous_snd.comp zcont)).continuousAt
  refine ⟨cont.congr_of_eventuallyEq ?_,?_⟩
  · filter_upwards [isOpen_nonzeroSignedTriads.mem_nhds hp,firstAt.eventually_ne active₁,
      secondAt.eventually_ne active₂] with z hz ha hb
    exact same hz ha hb
  · rw [same hp active₁ active₂]
    simpa only [norm_iteratedFDeriv_zero] using hJets k hk 0 (by decide) _ inBox

/-- Positive-ratio atlas data and the actual comparable boxes yield the
regularity required by the unscaled original-symbol entrance. -/
theorem analyticNearOriginalSymbol_of_positiveAtlas_boxes (ϑ : ℝ → ℝ) (hϑ : Continuous ϑ)
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0) {κ b A : ℝ} (hκ : 0 < κ) (hκsmall : κ < 1/16)
    (hb : 7*κ/4 < b) (hA : 0 ≤ A) (m : Joint → ℂ)
    (hom : ∀ t : ℝ, 0 < t → ∀ p ∈ nonzeroSignedTriads, m (t • p) = m p)
    (atlas : AnalyticNearPositiveAtlas ϑ κ b A m) {N : ℕ} (cover : AnalyticNearComparableCoverage ϑ κ N)
    (boxes : AnalyticNearComparableBudget N A (radianFourBranchSymbol ϑ κ m 3)) :
    AnalyticNearOriginalSymbol m := by
  apply analyticNearOriginalSymbol_of_localFourBranches ϑ hϑ hκ m hA hom
  intro i p hp active
  fin_cases i
  · exact lowBranch_local_data ϑ hCut hκ hκsmall hb m hom atlas 0 hp active
  · exact lowBranch_local_data ϑ hCut hκ hκsmall hb m hom atlas 1 hp active
  · exact lowBranch_local_data ϑ hCut hκ hκsmall hb m hom atlas 2 hp active
  · obtain ⟨j,k,hk,hp₁,hp₂⟩ := cover p hp active
    exact comparable_local_box_data ϑ κ m hom boxes hk hp hp₁ hp₂

end Burnett.A05

#print axioms Burnett.A05.analyticNearOriginalSymbol_of_localFourBranches
#print axioms Burnett.A05.exists_analyticNearComparableCoverage
#print axioms Burnett.A05.analyticNearOriginalSymbol_of_positiveAtlas_boxes
