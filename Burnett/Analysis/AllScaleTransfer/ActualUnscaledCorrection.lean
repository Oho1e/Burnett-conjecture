import Burnett.Analysis.AllScaleTransfer.LowPassCorrectionBound
import Burnett.Analysis.AllScaleTransfer.SphereEndpointBox

set_option autoImplicit false
set_option maxHeartbeats 5400000

noncomputable section

namespace Burnett.A05

open Set Metric MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier
open scoped ContDiff Nat

/-- For the unscaled chart the exact cutoff correction has the same
zero-ratio derivative budget as the endpoint, up to a fixed constant. -/
theorem exists_unscaled_radianLowPassCorrection_bound {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (l u : ℝ) (hl : 0 < l) (hu : 0 ≤ u) (hu1 : u < 1)
    (hOne : ∀ t, 0 ≤ t → t ≤ l → χ t = 1) (hZero : ∀ t, u ≤ t → χ t = 0) :
    ∃ (gap : ℕ) (C : ℝ), 3 ≤ gap ∧ 0 ≤ C ∧
      ∀ (M₀ : Joint → ℂ) (B : ℝ), 0 ≤ B →
      ContDiffOn ℝ 100 (sphereEndpointBoxPullback M₀) sphereEndpointAnnuli →
      (∀ n ≤ 40, ∀ z ∈ sphereEndpointAnnuli,
        ‖iteratedFDeriv ℝ n (sphereEndpointBoxPullback M₀) z‖ ≤ B) →
      ∀ f g w : SchwartzMap E ℂ,
        ‖radianTrilinearForm
          (fun p => ∑' j, radianLowPassCorrectionBlock χ (ContinuousLinearEquiv.refl ℝ E) gap M₀ j p)
          f g w‖ ≤ C * B * (triLpMass f g w 3 3 3).toReal := by
  classical
  obtain ⟨gap,H,C₀,hGap,_,hC₀,box⟩ := exists_radianLowPassCorrection_bound
    5 1 1 l u (by norm_num) zero_lt_one zero_lt_one hl hu hu1 hOne hZero
  let I := lowPassCorrectionShifts gap H
  let A := ContinuousLinearEquiv.refl ℝ E
  let band := {p : E | (1/2 : ℝ) ≤ ‖p‖ ∧ ‖p‖ ≤ 2}
  let K := band ×ˢ band
  let V := {p : E | (1/4 : ℝ) < ‖p‖ ∧ ‖p‖ < 3} ×ˢ {q : E | (1/4 : ℝ) < ‖q‖ ∧ ‖q‖ < 3}
  have hBand : IsCompact band :=
    (isCompact_closedBall (0 : E) 2).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const))
      (fun _ hz => mem_closedBall_zero_iff.mpr hz.2)
  have hOpenBand : IsOpen {p : E | (1/4 : ℝ) < ‖p‖ ∧ ‖p‖ < 3} :=
    (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
  have hKV : K ⊆ V := by
    rintro p ⟨⟨h1,h2⟩,⟨h3,h4⟩⟩
    exact ⟨⟨(by norm_num : (1/4 : ℝ) < 1/2).trans_le h1,h2.trans_lt (by norm_num)⟩,
      ⟨(by norm_num : (1/4 : ℝ) < 1/2).trans_le h3,h4.trans_lt (by norm_num)⟩⟩
  obtain ⟨β',hβ',compactβ',insideβ',oneβ'⟩ := exists_fixed_annular_cutoff
    (hBand.prod hBand) (hOpenBand.prod hOpenBand) hKV
  let β (z : BoxSpace) := β' (boxToPair z)
  have hβ : ContDiff ℝ ∞ β := hβ'.comp boxToPair.contDiff
  let Kβ := boxToPair.symm '' tsupport β'
  have compactKβ : IsCompact Kβ := compactβ'.image boxToPair.symm.continuous
  have suppβ : tsupport β ⊆ Kβ := by
    apply closure_minimal ?_ compactKβ.isClosed
    intro z hz
    exact ⟨boxToPair z,subset_tsupport _ hz,boxToPair.symm_apply_apply z⟩
  have annulus : boxToPair ⁻¹' V = sphereEndpointAnnuli := by
    ext z
    constructor
    · rintro ⟨⟨a,b⟩,⟨c,d⟩⟩
      exact ⟨a,b,c,d⟩
    · rintro ⟨a,b,c,d⟩
      exact ⟨⟨a,b⟩,⟨c,d⟩⟩
  have openAnn : IsOpen sphereEndpointAnnuli :=
    annulus ▸ (hOpenBand.prod hOpenBand).preimage boxToPair.continuous
  have Kβ_ann : Kβ ⊆ sphereEndpointAnnuli := by
    rintro z ⟨p,hp,rfl⟩
    rw [← annulus]
    change boxToPair (boxToPair.symm p) ∈ V
    rw [boxToPair.apply_symm_apply]
    exact insideβ' hp
  have hNZ (z : BoxSpace) (hz : z ∈ sphereEndpointAnnuli) :
      firstInput z ≠ 0 ∧ secondInput z ≠ 0 :=
    ⟨norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans hz.1),
      norm_pos_iff.mp ((by norm_num : (0 : ℝ) < 1/4).trans hz.2.2.1)⟩
  obtain ⟨D,hD,jetβ⟩ := exists_compact_contDiffOn_jet_bound compactKβ isOpen_univ
    (subset_univ _) hβ.contDiffOn 40
  let Q (k : ℤ) (z : BoxSpace) : ℂ :=
    ((χ ((2 : ℝ)^k * (‖firstInput z‖ / ‖secondInput z‖)) -
      radialBallBump ((2 : ℝ)^((gap : ℤ)+k) • firstInput z) : ℝ) : ℂ)
  have hQ (k : ℤ) : ContDiffOn ℝ ∞ (Q k) sphereEndpointAnnuli := by
    have hF : ContDiff ℝ ∞ firstInput := boxToPair.contDiff.fst
    have hG : ContDiff ℝ ∞ secondInput := boxToPair.contDiff.snd
    have nF := hF.contDiffOn.norm ℝ (fun z hz => (hNZ z hz).1)
    have nG := hG.contDiffOn.norm ℝ (fun z hz => (hNZ z hz).2)
    have ratio := nF.div nG (fun z hz => norm_ne_zero_iff.mpr (hNZ z hz).2)
    have res : ContDiffOn ℝ ∞
        (fun z => (2 : ℝ)^k * (‖firstInput z‖ / ‖secondInput z‖)) sphereEndpointAnnuli :=
      contDiffOn_const.mul ratio
    have lo : ContDiff ℝ ∞ (fun z : BoxSpace => radialBallBump ((2 : ℝ)^((gap : ℤ)+k) • firstInput z)) :=
      radialBallBump.contDiff.comp (contDiff_const.smul hF)
    exact Complex.ofRealCLM.contDiff.comp_contDiffOn ((hχ.comp_contDiffOn res).sub lo.contDiffOn)
  obtain ⟨Qb,hQb,Qjets⟩ : ∃ J : ℝ, 0 ≤ J ∧
      ∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ Kβ, ‖iteratedFDeriv ℝ n (Q k) z‖ ≤ J := by
    choose J hJ jets using fun k : (↑I : Type) =>
      exists_compact_contDiffOn_jet_bound compactKβ openAnn Kβ_ann (hQ k) 40
    refine ⟨∑ k, J k,Finset.sum_nonneg (fun k _ => hJ k),?_⟩
    intro k hk n hn z hz
    let i : (↑I : Type) := ⟨k,hk⟩
    exact (jets i n hn z hz).trans
      (Finset.single_le_sum (f := J) (fun j _ => hJ j) (Finset.mem_univ i))
  let L := (2 : ℝ)^40 * Qb
  let LC := (2 : ℝ)^40 * D * L
  have hL : 0 ≤ L := by unfold L; positivity
  have hLC : 0 ≤ LC := by unfold LC; positivity
  refine ⟨gap,C₀ * LC,hGap,mul_nonneg hC₀ hLC,?_⟩
  intro M₀ B hB hM bM f g w
  let raw (k : ℤ) := normalizedLowPassCorrection χ A gap M₀ k
  have hRaw (k : ℤ) : ContDiffOn ℝ 100 (raw k) sphereEndpointAnnuli :=
    hM.mul ((hQ k).of_le (WithTop.coe_le_coe.mpr le_top))
  have jRaw (k : ℤ) (hk : k ∈ I) (n : ℕ) (hn : n ≤ 40) (z : BoxSpace) (hz : z ∈ tsupport β) :
      ‖iteratedFDeriv ℝ n (raw k) z‖ ≤ L * B := by
    have hzK := suppβ hz
    have hzAnn := Kβ_ann hzK
    have eN : (n : WithTop ℕ∞) ≤ 100 := by exact_mod_cast (show n ≤ 100 by omega)
    rw [← iteratedFDerivWithin_of_isOpen n openAnn hzAnn]
    refine (norm_iteratedFDerivWithin_mul_le hM
      ((hQ k).of_le (WithTop.coe_le_coe.mpr le_top)) openAnn.uniqueDiffOn hzAnn eN).trans ?_
    calc
      _ ≤ ∑ j ∈ Finset.range (n+1), (n.choose j : ℝ) * B * Qb := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := (Finset.mem_range.mp hj)
        rw [iteratedFDerivWithin_of_isOpen j openAnn hzAnn,
          iteratedFDerivWithin_of_isOpen (n-j) openAnn hzAnn]
        exact mul_le_mul (mul_le_mul_of_nonneg_left (bM j (by omega) z hzAnn) (by positivity))
          (Qjets k hk (n-j) ((Nat.sub_le n j).trans hn) z hzK) (norm_nonneg _) (by positivity)
      _ = (2 : ℝ)^n * B * Qb := by
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        norm_cast
        rw [Nat.sum_range_choose]
      _ ≤ L * B := by
        unfold L
        rw [mul_right_comm ((2 : ℝ)^n) B Qb]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hn) hQb) hB
  have estimates (k : ℤ) (hk : k ∈ I) :=
    normalizedLowPassCorrection_cutoff_profile χ A gap M₀ k β hβ openAnn (suppβ.trans Kβ_ann)
      (hRaw k) D (L*B) hD (mul_nonneg hL hB) (fun n hn z hz => jetβ n hn z (suppβ hz))
      (jRaw k hk) (fun ζ υ hζ hυ _ => by
        have h1 := endpointHighProfile_properties.2.2 ζ hζ
        have h2 := endpointHighProfile_properties.2.2 υ hυ
        exact oneβ' _ (by simpa only [boxToPair_joined] using
          (show (ζ,υ) ∈ K from ⟨⟨h1.1.le,h1.2.le⟩,⟨h2.1.le,h2.2.le⟩⟩)))
  let G (k : ℤ) (z : BoxSpace) := β z • raw k z
  have result := box A (fun x => by simp [A]) M₀ (fun _ _ _ => by simp [A])
    G (LC*B) (mul_nonneg hLC hB) (fun k hk => (estimates k hk).1.contDiffOn)
    (fun k hk n hn z _ => by simpa only [LC,G,raw,mul_assoc] using (estimates k hk).2.1 n hn z)
    (fun k hk => (estimates k hk).2.2) f g w
  simpa only [A,mul_assoc] using result.2

end Burnett.A05
