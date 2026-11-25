import Burnett.Analysis.AllScaleTransfer.ActualFiniteShiftRemainder
import Burnett.Analysis.AllScaleTransfer.ActualAtlasBoxProfiles

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric Burnett.Analysis Burnett.Analysis.CapFourier
open Burnett.A02.FrequencySplit
open scoped ContDiff

private theorem radialAnnulusPair_compact (lo hi : ℝ) :
    IsCompact (radialJetAnnulus lo hi ×ˢ radialJetAnnulus lo hi) := by
  have h : IsCompact (radialJetAnnulus lo hi) :=
    (isCompact_closedBall (0 : Frequency) hi).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun _ hx => mem_closedBall_zero_iff.mpr hx.2)
  exact h.prod h

/-- In the original coordinates, the same fixed finite atlas supplies the
finite signed radial offsets of the actual ratio remainder. The common
positive-ratio matching includes zeros of the source symbol. -/
theorem exists_unscaled_atlas_finite_shift_remainder_bound
    {ι : Type*} [Fintype ι] (I : Finset ℤ)
    (V : ι → Set FrequencyPair) (U : ι → Set LowRatio.Angles)
    (angular : ι → FrequencyPair → LowRatio.Angles)
    (hV : ∀ i, IsOpen (V i)) (hU : ∀ i, IsOpen (U i))
    (hCover : radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2 ⊆ ⋃ i, V i)
    (hAnn : ∀ i, V i ⊆ radialJetAnnulus (1/4) 3 ×ˢ radialJetAnnulus (1/4) 3)
    (hAngular : ∀ i, ContDiffOn ℝ ∞ (angular i) (V i)) (hMap : ∀ i, MapsTo (angular i) (V i) (U i))
    {u b : ℝ} (hu : 0 < u) (hu1 : u < 1) (hub : u < b)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ ∞ χ) (hχ0 : χ 0 = 1) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (M : ι → LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
      (∀ i, ContDiffOn ℝ 100 (M i) (U i ×ˢ Ico (0 : ℝ) b)) →
      (∀ i n, n ≤ 100 → ∀ z ∈ U i ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (M i) (U i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A₁₀₀) →
      ∀ (m : Joint → ℂ), (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      (∀ i pq, pq ∈ V i → ∀ t : ℝ, 0 < t →
        let ρ := t * (‖pq.1‖ / ‖pq.2‖)
        ρ ∈ Ioo (0 : ℝ) b → m (t • pq.1, pq.2) =
          ρ • LowRatio.remainder (M i) χ (angular i pq, ρ)) →
      ∀ (f g h : SchwartzMap E ℂ),
      (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → m p ≠ 0 → ‖p.1‖ / ‖p.2‖ ≤ u) →
      let T (k : ℤ) := radianTrilinearForm (radianSignedGapSymbol m k) f g h
      ‖∑ k ∈ I, T k‖ ≤ C * A₁₀₀ * (triLpMass f g h 3 3 3).toReal := by
  classical
  let A := ContinuousLinearEquiv.refl ℝ Frequency
  let radialPair := radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2
  let K := boxToPair.symm '' radialPair
  let Vbox (i : ι) := boxToPair ⁻¹' V i
  have hK : IsCompact K := (radialAnnulusPair_compact (1/2) 2).image boxToPair.symm.continuous
  have inK (z : BoxSpace) : z ∈ K ↔ boxToPair z ∈ radialPair := by
    constructor
    · rintro ⟨pq,hpq,he⟩
      rw [← he, boxToPair.apply_symm_apply]
      exact hpq
    · intro hz
      exact ⟨boxToPair z,hz,boxToPair.symm_apply_apply z⟩
  have cover : K ⊆ ⋃ i, Vbox i := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp (hCover ((inK z).mp hz))
    exact mem_iUnion.mpr ⟨i,hi⟩
  obtain ⟨w,D,hD,hWSmooth,hWSupport,hWOne,hWJet⟩ := exists_box_chart_weights hK Vbox
    (fun i => (hV i).preimage boxToPair.continuous) cover 5
  let Kloc (i : ι) := boxToPair '' (K ∩ tsupport (w i))
  have compactKloc (i : ι) : IsCompact (Kloc i) :=
    (hK.inter_right (isClosed_tsupport (w i))).image boxToPair.continuous
  have inV (i : ι) : Kloc i ⊆ V i := by
    rintro pq ⟨z,hz,rfl⟩
    exact hWSupport i hz.2
  let Wide := radialJetAnnulus (1/4) 3 ×ˢ radialJetAnnulus (1/4) 3
  let Off : Set FrequencyPair := {pq | pq.1 ≠ 0} ∩ {pq | pq.2 ≠ 0}
  have hOff : IsOpen Off :=
    (isOpen_ne_fun continuous_fst continuous_const).inter (isOpen_ne_fun continuous_snd continuous_const)
  have wideOff : Wide ⊆ Off := by
    intro pq hp
    have hlo : (0 : ℝ) < 1/4 := by norm_num
    exact ⟨norm_pos_iff.mp (hlo.trans_le hp.1.1),norm_pos_iff.mp (hlo.trans_le hp.2.1)⟩
  have smoothR : ContDiffOn ℝ ∞ (physicalRadialRatio A.toContinuousLinearMap) Off := by
    intro pq hp
    exact (physicalRadialRatio_contDiffAt A.toContinuousLinearMap hp.1 hp.2).contDiffWithinAt
  obtain ⟨B,hB,bR⟩ := exists_compact_contDiffOn_jet_bound
    (radialAnnulusPair_compact (1/4) 3) hOff wideOff smoothR 40
  have chart (i : ι) := exists_finite_shift_remainder_boxes I B hB
    (compactKloc i) (hV i) (inV i) (fun pq hp => wideOff (hAnn i hp))
    (hU i) (angular i) (hAngular i) (hMap i) hu hub χ hχ
  choose η d hd hOne hZero build using chart
  obtain ⟨_,Cbox,hCbox,box⟩ := exists_finite_shift_remainder_bound_of_profiles I
    1 1 u zero_lt_one zero_lt_one hu hu1
  let Cext := (2 : ℝ)^40 * D * ∑ i, d i
  have hCext : 0 ≤ Cext :=
    mul_nonneg (mul_nonneg (by positivity) hD) (Finset.sum_nonneg (fun i _ => hd i))
  refine ⟨(I.card : ℝ) * Cbox * Cext, by positivity, ?_⟩
  intro M A₁₀₀ hA₁₀₀ smooth jets m hom source f g h hLow T
  have data (i : ι) := build i A (fun n hn pq hp => bR n hn pq (hAnn i hp))
    (M i) A₁₀₀ hA₁₀₀ (smooth i) (jets i)
  choose G hGSmooth _hGOutside hGJet hGEq using data
  let Gsum (k : ℤ) (z : BoxSpace) : ℂ := ∑ i, w i z • G i k z
  have hWeighted (i : ι) (k : ℤ) : ContDiff ℝ 100 (fun z => w i z • G i k z) :=
    ((hWSmooth i).of_le (by decide : (100 : WithTop ℕ∞) ≤ ∞)).smul (hGSmooth i k)
  have hSumSmooth (k : ℤ) : ContDiff ℝ 100 (Gsum k) :=
    ContDiff.sum (fun i _ => hWeighted i k)
  have hSumJet (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40)
      (z : BoxSpace) (hz : z ∈ ball (0 : BoxSpace) 5) :
      ‖iteratedFDeriv ℝ n (Gsum k) z‖ ≤ Cext * A₁₀₀ := by
    have hn' : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (hn.trans (by decide : 40 ≤ 100))
    have hTerm (i : ι) : ‖iteratedFDeriv ℝ n (fun z => w i z • G i k z) z‖ ≤
        (2 : ℝ)^40 * D * (d i * A₁₀₀) := by
      have prod := norm_iteratedFDeriv_smul_le
        ((hWSmooth i).of_le (by decide : (100 : WithTop ℕ∞) ≤ ∞)) (hGSmooth i k) z hn'
      refine prod.trans ?_
      calc
        _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * D * (d i * A₁₀₀) := by
          apply Finset.sum_le_sum
          intro j hj
          have hj' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
          exact mul_le_mul
            (mul_le_mul_of_nonneg_left (hWJet i j (hj'.trans hn) z (ball_subset_closedBall hz)) (by positivity))
            (hGJet i k hk (n-j) ((Nat.sub_le n j).trans hn) z) (norm_nonneg _) (by positivity)
        _ = (2 : ℝ)^n * D * (d i * A₁₀₀) := by
          rw [← Finset.sum_mul, ← Finset.sum_mul]
          norm_cast
          rw [Nat.sum_range_choose]
        _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_right₀ (by norm_num) hn) hD) (mul_nonneg (hd i) hA₁₀₀)
    have eq := iteratedFDeriv_sum (u := (Finset.univ : Finset ι))
      (f := fun i z => w i z • G i k z) (i := n) (fun i _ => (hWeighted i k).of_le hn')
    change ‖iteratedFDeriv ℝ n (fun z => ∑ i, w i z • G i k z) z‖ ≤ _
    rw [eq, Finset.sum_apply]
    calc
      _ ≤ ∑ i, (2 : ℝ)^40 * D * (d i * A₁₀₀) := norm_sum_le_of_le _ (fun i _ => hTerm i)
      _ = _ := by simp only [Cext, ← mul_assoc, Finset.mul_sum, Finset.sum_mul]
  have matchG (k : ℤ) (_hk : k ∈ I) (j : ℤ) (p : Joint)
      (hTest : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hp : integerRadialWindow (j+k) p.1 ≠ 0) (hq : integerRadialWindow j p.2 ≠ 0) :
      Gsum k (joinedInputs ((2 : ℝ)^(-(j+k)) • p.1) ((2 : ℝ)^(-j) • p.2)) = m p := by
    let ζ := (2 : ℝ)^(-(j+k)) • p.1
    let υ := (2 : ℝ)^(-j) • p.2
    let z := joinedInputs ζ υ
    let ρ := ‖p.1‖ / ‖p.2‖
    have narrow (l : ℤ) (x : E) (hx : integerRadialWindow l x ≠ 0) :
        (2 : ℝ)^(-l) • x ∈ radialJetAnnulus (1/2) 2 := by
      have hn : endpointHighProfile ((2 : ℝ)^(-l) • x) ≠ 0 := by
        rw [endpointHighProfile_eq_integerRadialWindow]
        exact_mod_cast hx
      have H := endpointHighProfile_properties.2.2 _ hn
      exact ⟨H.1.le,H.2.le⟩
    have hz : z ∈ K := (inK z).mpr (by
      change boxToPair (joinedInputs ζ υ) ∈ radialPair
      rw [boxToPair_joined]
      exact ⟨narrow _ _ hp,narrow _ _ hq⟩)
    have hρ : 0 < ρ := by
      have pos (l : ℤ) (x : E) (hx : integerRadialWindow l x ≠ 0) : 0 < ‖x‖ :=
        norm_pos_iff.mpr (fun e => hx (by rw [e, integerRadialWindow_zero]))
      exact div_pos (pos _ _ hp) (pos _ _ hq)
    have ratio : fixedShiftPhysicalRatio A k (ζ,υ) = ρ :=
      fixedShiftPhysicalRatio_at_frequencies A k j p.1 p.2
    have restore (l : ℤ) (x : E) : (2 : ℝ)^l • ((2 : ℝ)^(-l) • x) = x := by
      rw [smul_smul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero, one_smul]
    have scaled : (2 : ℝ)^j • ((2 : ℝ)^k • ζ, υ) = p := by
      apply Prod.ext
      · change (2 : ℝ)^j • ((2 : ℝ)^k • ζ) = p.1
        rw [smul_smul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
        exact restore _ _
      · exact restore _ _
    have same : m ((2 : ℝ)^k • ζ, υ) = m p :=
      (hom ((2 : ℝ)^j) (by positivity) _).symm.trans (congrArg m scaled)
    have value (i : ι) (hi : w i z ≠ 0) : G i k z = m p := by
      have hpq : (ζ,υ) ∈ Kloc i := ⟨z,⟨hz,subset_tsupport (w i) hi⟩,boxToPair_joined ζ υ⟩
      change G i k (joinedInputs ζ υ) = m p
      rw [hGEq i k ζ υ hpq, ratio, cutoffRemainderNumerator_eq_ratio_remainder _ χ (η i) hχ0]
      by_cases hrb : ρ < b
      · have scaleRatio : (2 : ℝ)^k * (‖ζ‖ / ‖υ‖) = ρ := ratio
        have hr : (2 : ℝ)^k * (‖ζ‖ / ‖υ‖) ∈ Ioo (0 : ℝ) b := by
          rw [scaleRatio]
          exact ⟨hρ,hrb⟩
        have he : m ((2 : ℝ)^k • ζ,υ) =
            ρ • LowRatio.remainder (M i) χ (angular i (ζ,υ),ρ) := by
          simpa only [scaleRatio] using source i (ζ,υ) (inV i hpq) ((2 : ℝ)^k) (by positivity) hr
        rw [← he,same]
        by_cases hn : m p = 0
        · rw [hn,smul_zero]
        · rw [hOne i ρ ⟨hρ.le,hLow p hTest hn⟩,one_smul]
      · have hn : m p = 0 := by
          by_contra he
          exact hrb ((hLow p hTest he).trans_lt hub)
        rw [hZero i ρ (le_of_not_gt hrb),zero_smul,hn]
    change Gsum k z = m p
    calc
      _ = ∑ i, w i z • m p := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : w i z = 0
        · simp only [hi,zero_smul]
        · rw [value i hi]
      _ = (∑ i, w i z) • m p := by rw [Finset.sum_smul]
      _ = _ := by rw [hWOne z hz,one_smul]
  have hActive (p : Joint) (ht : radianWeight (fun _ => 1) f g h p ≠ 0) (hm : m p ≠ 0) :
      1 * ‖p.1‖ ≤ ‖A p.1‖ ∧ 1 * ‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.1‖ / ‖A p.2‖ ≤ u := by
    exact ⟨by simp [A],by simp [A],hLow p ht hm⟩
  have result := box A (fun p => by simp [A]) m Gsum (Cext * A₁₀₀) (mul_nonneg hCext hA₁₀₀)
    (fun k _ => (hSumSmooth k).contDiffOn) hSumJet f g h hActive matchG
  simpa only [mul_assoc] using result.2

end Burnett.A05.BoxFourier
