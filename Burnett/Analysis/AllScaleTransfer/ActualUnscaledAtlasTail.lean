import Burnett.Analysis.AllScaleTransfer.ActualAtlasBoxProfiles
import Burnett.Analysis.AllScaleTransfer.UnscaledPositiveBoxExtension
import Burnett.Analysis.AllScaleTransfer.RadianDyadicRemainderTail

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric MeasureTheory
open Burnett.Analysis CapFourier
open Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal

private def radialPair : Set FrequencyPair := radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2

private theorem radialPair_compact : IsCompact radialPair := by
  have h : IsCompact (radialJetAnnulus (1/2) 2 : Set Frequency) :=
    (isCompact_closedBall (0 : Frequency) 2).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun _ hx => mem_closedBall_zero_iff.mpr hx.2)
  exact h.prod h

/-- The unscaled low-ratio tail of the original Fourier form uses the
fixed finite angular atlas. The same estimate holds without any cap
localization, using the original one-sided angular-ratio data. -/
theorem exists_unscaled_atlas_dyadic_remainder_tail_bound
    {ι : Type*} [Fintype ι] (V : ι → Set FrequencyPair) (U : ι → Set LowRatio.Angles)
    (angular : ι → FrequencyPair → LowRatio.Angles)
    (hV : ∀ i, IsOpen (V i)) (hU : ∀ i, IsOpen (U i))
    (hCover : radialJetAnnulus (1/2) 2 ×ˢ radialJetAnnulus (1/2) 2 ⊆ ⋃ i, V i)
    (hAnn : ∀ i, V i ⊆ radialJetAnnulus (1/4) 3 ×ˢ radialJetAnnulus (1/4) 3)
    (hAngular : ∀ i, ContDiffOn ℝ ∞ (angular i) (V i)) (hMap : ∀ i, MapsTo (angular i) (V i) (U i))
    (b : ℝ) (hb : 0 < b) (χ₀ : ℝ → ℝ) (oneχ₀ : χ₀ 0 = 1)
    (plateau : ∀ ρ ∈ Ioo (0 : ℝ) b, χ₀ ρ = 1) :
    ∃ (cutoff : ℕ) (C : ℝ), 4 ≤ cutoff ∧ 0 ≤ C ∧
      ∀ (M : ι → LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
      (∀ i, ContDiffOn ℝ 100 (M i) (U i ×ˢ Ico (0 : ℝ) b)) →
      (∀ i n, n ≤ 100 → ∀ z ∈ U i ×ˢ Ico (0 : ℝ) b,
        ‖iteratedFDerivWithin ℝ n (M i) (U i ×ˢ Ico (0 : ℝ) b) z‖ ≤ A₁₀₀) →
      ∀ (m : Joint → ℂ), (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
      (∀ i pq, pq ∈ V i → ∀ t : ℝ, 0 < t →
        let ρ := t * (‖pq.1‖ / ‖pq.2‖)
        ρ ∈ Ioo (0 : ℝ) b → m (t • pq.1, pq.2) =
          ρ • LowRatio.remainder (M i) χ₀ (angular i pq, ρ)) →
      ∀ (f g h : SchwartzMap E ℂ),
      let T (s : {s : ℕ // cutoff ≤ s}) := radianTrilinearForm (radianLowGapSymbol m s.val) f g h
      let Mass := (triLpMass f g h 3 3 3).toReal
      (∀ s, ‖T s‖ ≤ C * A₁₀₀ * radialGapDecay s.val * Mass) ∧
      Summable (fun s => ‖T s‖) ∧
      ‖∑' s, T s‖ ≤ C * A₁₀₀ * (radialGapDecay cutoff * 2) * Mass := by
  classical
  let K := boxToPair.symm '' radialPair
  let Vbox (i : ι) := boxToPair ⁻¹' V i
  have hK : IsCompact K := radialPair_compact.image boxToPair.symm.continuous
  have hVbox (i : ι) : IsOpen (Vbox i) := (hV i).preimage boxToPair.continuous
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
  obtain ⟨ρ,D,hD,hρSmooth,hρSupport,hρOne,hρJet⟩ := exists_box_chart_weights hK Vbox hVbox cover 5
  let Kloc (i : ι) := boxToPair '' (K ∩ tsupport (ρ i))
  have hKloc (i : ι) : IsCompact (Kloc i) :=
    (hK.inter_right (isClosed_tsupport (ρ i))).image boxToPair.continuous
  have inV (i : ι) : Kloc i ⊆ V i := by
    rintro pq ⟨z,hz,rfl⟩
    exact hρSupport i hz.2
  have chart (i : ι) := exists_unscaled_positive_annular_box_extension (by norm_num : 0 < (1/4 : ℝ))
    (hKloc i) (hV i) (inV i) (hAnn i) (hU i) (angular i) (hAngular i) (hMap i) hb χ₀ oneχ₀ plateau
  choose d s₀ hd hChart using chart
  let cutoff := 4 + ∑ i, s₀ i
  have hc : 4 ≤ cutoff := by unfold cutoff; omega
  have hEarly (i : ι) : s₀ i ≤ cutoff := by
    have H : s₀ i ≤ ∑ k, s₀ k :=
      Finset.single_le_sum (f := s₀) (fun k _ => Nat.zero_le (s₀ k)) (Finset.mem_univ i)
    unfold cutoff
    omega
  obtain ⟨Cbox,hCbox,hBox⟩ := exists_radianTrilinearForm_dyadic_remainder_tail_bound 5 (by norm_num)
  let C₀ := (2 : ℝ)^40 * D * ∑ i, d i
  have hC₀ : 0 ≤ C₀ := by unfold C₀; exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => hd i))
  refine ⟨cutoff,Cbox*C₀,hc,mul_nonneg hCbox hC₀,?_⟩
  intro M A₁₀₀ hA hSmooth hJet m hHom hSymbol f g h T Mass
  have data (i : ι) := hChart i (M i) A₁₀₀ hA (hSmooth i) (hJet i)
  choose G hGSmooth hGJet hGMatch hGPos using data
  let original (s : ℕ) (z : BoxSpace) : ℂ :=
    m (radialGapDecay s • (boxToPair z).1, (boxToPair z).2)
  have hPoints (i : ι) (s : ℕ) (hs : cutoff ≤ s) (z : BoxSpace) (hz : z ∈ K) (hzρ : ρ i z ≠ 0) :
      G i s z = original s z := by
    let p := boxToPair z
    have hLoc : p ∈ Kloc i := ⟨z,⟨hz,subset_tsupport (ρ i) hzρ⟩,rfl⟩
    have hv := inV i hLoc
    have hs' := (hEarly i).trans hs
    have he : joinedInputs p.1 p.2 = z := by
      apply boxToPair.injective
      exact boxToPair_joined p.1 p.2
    have hρ := hGPos i s hs' p.1 p.2 hv
    have hρ' : radialGapDecay s * (‖p.1‖ / ‖p.2‖) ∈ Ioo (0 : ℝ) b := by
      simpa only [gapRatio,ContinuousLinearEquiv.refl_apply] using hρ
    have hRem : normalizedGapRemainder (ContinuousLinearEquiv.refl ℝ Frequency)
          (angular i ∘ boxToPair) (M i) χ₀ s (joinedInputs p.1 p.2) =
        (radialGapDecay s * (‖p.1‖ / ‖p.2‖)) •
          LowRatio.remainder (M i) χ₀ (angular i p,radialGapDecay s * (‖p.1‖ / ‖p.2‖)) := by
      simp only [normalizedGapRemainder,firstInput_joined,secondInput_joined,gapRatio,
        ContinuousLinearEquiv.refl_apply,Function.comp_apply,boxToPair_joined]
    have hValue := (hGMatch i s hs' p.1 p.2 hLoc).trans hRem
    rw [he] at hValue
    exact hValue.trans (hSymbol i p hv (radialGapDecay s) (by unfold radialGapDecay; positivity) hρ').symm
  obtain ⟨hSumSmooth,hSumJet,hSumEq⟩ := weighted_atlas_box_profiles_sum K 5 cutoff ρ D hD
    hρSmooth hρOne hρJet G (fun i => d i * A₁₀₀) (fun i => mul_nonneg (hd i) hA) hGSmooth
    (fun i s n hn z _ => hGJet i s n hn z) original hPoints
  let Gsum (s : ℕ) (z : BoxSpace) := ∑ i, ρ i z • G i s z
  have hSumBound (s n : ℕ) (hn : n ≤ 40) (z : BoxSpace) (hz : z ∈ ball (0 : BoxSpace) 5) :
      ‖iteratedFDeriv ℝ n (Gsum s) z‖ ≤ (C₀*A₁₀₀) * radialGapDecay s := by
    simpa only [C₀,Gsum,Finset.sum_mul,mul_assoc] using hSumJet s n hn z (ball_subset_closedBall hz)
  have hMatch (s : ℕ) (hs : cutoff ≤ s) (j : ℤ) (p : Joint) (_ : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hp : integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0) (hq : integerRadialWindow j p.2 ≠ 0) :
      Gsum s (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = m p := by
    let ζ := ((2 : ℝ)^(-(j - (s : ℤ)))) • p.1
    let υ := ((2 : ℝ)^(-j)) • p.2
    have narrow (k : ℤ) (x : E) (hx : integerRadialWindow k x ≠ 0) :
        ((2 : ℝ)^(-k)) • x ∈ radialJetAnnulus (1/2) 2 := by
      have hn : endpointHighProfile (((2 : ℝ)^(-k)) • x) ≠ 0 := by
        rw [endpointHighProfile_eq_integerRadialWindow]
        exact_mod_cast hx
      have H := endpointHighProfile_properties.2.2 _ hn
      exact ⟨H.1.le,H.2.le⟩
    let z := joinedInputs ζ υ
    have hz : z ∈ K := (inK z).mpr (by
      change boxToPair (joinedInputs ζ υ) ∈ radialPair
      rw [boxToPair_joined]
      exact ⟨narrow _ _ hp,narrow _ _ hq⟩)
    have hscale : (2 : ℝ)^j * radialGapDecay s = (2 : ℝ)^(j - (s : ℤ)) := by
      rw [radialGapDecay,div_pow,one_pow,one_div,zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0),zpow_natCast,
        div_eq_mul_inv]
    have restore (k : ℤ) (x : E) : ((2 : ℝ)^k) • (((2 : ℝ)^(-k)) • x) = x := by
      rw [smul_smul,← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0),add_neg_cancel,zpow_zero,one_smul]
    have hPhys : ((2 : ℝ)^j) • ((radialGapDecay s) • ζ,υ) = p := by
      apply Prod.ext
      · change ((2 : ℝ)^j) • ((radialGapDecay s) • ζ) = p.1
        rw [smul_smul,hscale]
        exact restore _ _
      · exact restore _ _
    change Gsum s z = m p
    refine (hSumEq s hs z hz).trans ?_
    have e : original s z = m (radialGapDecay s • ζ,υ) := by
      unfold original z
      rw [boxToPair_joined]
    exact e.trans ((hHom ((2 : ℝ)^j) (by positivity) _).symm.trans (congrArg m hPhys))
  have H := hBox cutoff hc m Gsum (C₀*A₁₀₀) (mul_nonneg hC₀ hA)
    (fun s => (hSumSmooth s).contDiffOn) hSumBound f g h hMatch
  simpa only [mul_assoc] using H

end Burnett.A05.BoxFourier
