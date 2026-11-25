import Burnett.Analysis.AllScaleTransfer.ComparableAxialBox

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.A05

open Set MeasureTheory Metric
open Burnett.A02.FrequencySplit Burnett.A05.BoxFourier
open Burnett.Analysis.CapFourier Burnett.Analysis.ProjectiveNullCaps
open scoped ContDiff

/-- The original comparable coefficient is estimated on the actual
three enlarged-cap factors. The given normalized C100 boxes are
localized by the three axial windows in the same cap coordinates. -/
theorem exists_actual_cap_radianComparable_box_bound {ϑ : ℝ → ℝ}
    (hCut : ∀ t : ℝ, 1 ≤ t → ϑ t = 0)
    (hFlat : ∀ t : ℝ, 0 ≤ t → t ≤ 1/4 → ϑ t = 1)
    (P B tube outer enlarged κ : ℝ) (hP : 4 < P)
    (hB : 0 < B) (hTube : 0 < tube) (hOut : 0 ≤ outer) (hOE : outer < enlarged)
    (hκ : 0 < κ) (hκsmall : κ < 1/16) :
    ∃ (N : ℕ) (C : ℝ), 0 ≤ C ∧
      ∀ (metric : Form) (u : Vec) (F : NullCapChart metric u),
        ‖u‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
        ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
        ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4*B*(5*δ) ≤ 1 →
          let A := capFrequencyEquiv F hδ.ne'
          let Pcap := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged u)
          let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
          ∀ (m : Joint → ℂ),
            (∀ p, m p ≠ 0 → comparableSlotWeight ϑ κ (A p.1) (A p.2) (A (-(p.1+p.2))) ≠ 0) →
            (∀ t : ℝ, 0 < t → ∀ p : Joint, m (t • p) = m p) →
            AEStronglyMeasurable m volume →
            ∀ (G : ℤ → BoxSpace → ℂ) (Q : ℝ), 0 ≤ Q →
              (∀ k ∈ I, ContDiffOn ℝ 100 (G k) (ball (0 : BoxSpace) P)) →
              (∀ k ∈ I, ∀ n ≤ 40, ∀ z ∈ ball (0 : BoxSpace) P,
                ‖iteratedFDeriv ℝ n (G k) z‖ ≤ Q) →
              (∀ k ∈ I, ∀ ζ υ : E, endpointHighProfile ζ ≠ 0 → endpointHighProfile υ ≠ 0 →
                G k (joinedInputs ζ υ) = m ((2 : ℝ)^k • ζ, υ)) →
              ∀ (f g h : SchwartzMap E ℂ),
                (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → A p.1 ∈ Pcap ∧
                  A p.2 ∈ Pcap ∧ A (-(p.1+p.2)) ∈ Pcap) →
                ‖radianTrilinearForm m f g h‖ ≤ C * Q * (triLpMass f g h 3 3 3).toReal := by
  obtain ⟨α,L,U,_,_,hL,hU,localize⟩ :=
    exists_actual_cap_comparable_axial_localization B tube outer enlarged hB hTube hOut hOE
  obtain ⟨N,C₀,hC₀,compBound⟩ := exists_radianComparable_box_bound
    hCut hFlat P κ L U hP hκ hκsmall hL hU
  let I := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let a := comparableRadialLower κ L U
  let b := comparableRadialUpper κ L U
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have hab : a ≤ b := (min_le_left _ _).trans
    ((show (1/2 : ℝ) ≤ 2 by norm_num).trans (le_max_left _ _))
  obtain ⟨D,hD,hBox⟩ := exists_comparable_axial_box_budget I α a b P ha hab
  refine ⟨N,C₀*D,mul_nonneg hC₀ hD,?_⟩
  intro metric u F hu hF hFI δ hδ hδ₁ hsmall A Pcap I' m hComp hHom hMeas G Q hQ sG bG eqG f g h hsupp
  obtain ⟨geometry,eqForm⟩ := localize metric u F hu hF hFI δ hδ hδ₁ hsmall
  let mAx := axialComparableSymbol α m
  have locComp (p : Joint) (hp : mAx p ≠ 0) :
      let w := -(p.1+p.2)
      comparableSlotWeight ϑ κ (A p.1) (A p.2) (A w) ≠ 0 ∧
      (L*‖p.1‖ ≤ ‖A p.1‖ ∧ ‖A p.1‖ ≤ U*‖p.1‖) ∧
      (L*‖p.2‖ ≤ ‖A p.2‖ ∧ ‖A p.2‖ ≤ U*‖p.2‖) ∧
      (L*‖w‖ ≤ ‖A w‖ ∧ ‖A w‖ ≤ U*‖w‖) := by
    have hm : m p ≠ 0 := fun e => hp (by simp only [mAx,axialComparableSymbol,e,mul_zero])
    have hW : axialComparableWindow α p ≠ 0 :=
      fun e => hp (by simp only [mAx,axialComparableSymbol,e,Complex.ofReal_zero,zero_mul])
    exact ⟨hComp p hm,geometry p hW⟩
  let H (k : ℤ) (z : BoxSpace) := comparableAxialBoxWindow α a b k z • G k z
  obtain ⟨sH,bH⟩ := hBox G Q hQ sG bG
  have hMatch (k : ℤ) (hk : k ∈ I) (ζ υ : E)
      (hζ : endpointHighProfile ζ ≠ 0) (hυ : endpointHighProfile υ ≠ 0) :
      H k (joinedInputs ζ υ) = mAx ((2 : ℝ)^k • ζ,υ) := by
    let p : Joint := ((2 : ℝ)^k • ζ,υ)
    let w := -(p.1+p.2)
    let K := comparableThirdCutoff (1/2) 2 1 ζ * comparableThirdCutoff (1/2) 2 1 υ *
      comparableThirdCutoff a b 1 w
    have eW : comparableAxialBoxWindow α a b k (joinedInputs ζ υ) = K * axialComparableWindow α p :=
      comparableAxialBoxWindow_joined α a b k ζ υ
    change comparableAxialBoxWindow α a b k (joinedInputs ζ υ) • G k (joinedInputs ζ υ) = mAx p
    rw [eW, eqG k hk ζ υ hζ hυ, mul_smul]
    change K • mAx p = mAx p
    by_cases h0 : mAx p = 0
    · rw [h0,smul_zero]
    obtain ⟨hc,cp,cq,cw⟩ := locComp p h0
    have ann (x : E) (hx : endpointHighProfile x ≠ 0) : (1/2 : ℝ) ≤ ‖x‖ ∧ ‖x‖ ≤ 2 := by
      have hz := endpointHighProfile_properties.2.2 x hx
      exact ⟨hz.1.le,hz.2.le⟩
    have hAnnQ : (1 : ℝ)/2 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 2*1 := by simpa only [mul_one] using ann υ hυ
    have hw : ‖w‖ ∈ Icc a b := by
      have hBand := comparable_normalized_triad_annulus hCut hFlat A hκ hκsmall hL hU
        (by norm_num : (0 : ℝ) < 1) hAnnQ hc cp cq cw
      simpa only [mul_one] using hBand.2.2
    have wζ : comparableThirdCutoff (1/2) 2 1 ζ = 1 := comparableThirdCutoff_eq_one
      (by norm_num) (by norm_num) (by norm_num) (by simpa only [mul_one] using ann ζ hζ)
    have wυ : comparableThirdCutoff (1/2) 2 1 υ = 1 := comparableThirdCutoff_eq_one
      (by norm_num) (by norm_num) (by norm_num) (by simpa only [mul_one] using ann υ hυ)
    have ww : comparableThirdCutoff a b 1 w = 1 :=
      comparableThirdCutoff_eq_one ha (ha.trans_le hab) (by norm_num) (by simpa only [mul_one] using hw)
    simp only [K,wζ,wυ,ww,mul_one,one_smul]
  have Hbound := compBound A mAx locComp (axialComparableSymbol_pos_smul α hHom)
    (axialComparableSymbol_aestronglyMeasurable α hMeas) H (D*Q) (mul_nonneg hD hQ) sH bH hMatch f g h
  rw [← eqForm f g h hsupp m]
  simpa only [mul_assoc] using Hbound

end Burnett.A05
