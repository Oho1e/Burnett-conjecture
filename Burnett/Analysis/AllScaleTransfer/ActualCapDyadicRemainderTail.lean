import Burnett.Analysis.AllScaleTransfer.ActualSignedBoxSum
import Burnett.Analysis.AllScaleTransfer.RadianDyadicRemainderTail

set_option autoImplicit false
set_option maxHeartbeats 7000000

noncomputable section

namespace Burnett.A05.BoxFourier

open Set Metric MeasureTheory
open Burnett.Analysis CapFourier ProjectiveNullCaps
open Burnett.A02.FrequencySplit
open scoped ContDiff ENNReal

private theorem signedAxis_smul (t : ℝ) (sign : Bool) (p : Frequency) :
    signedAxis sign (t • p) = t * signedAxis sign p := by
  cases sign
  · change -(t * p 0) = t * -(p 0)
    ring
  · rfl

private theorem signedAxis_pos_of_normalized {α : ℝ} (hα : 0 < α)
    (p : Frequency) (i : ℤ) (sign : Bool) (H : ((2 : ℝ)^(-i)) • p ∈ signedClosedAnnulus α sign) :
    0 < signedAxis sign p := by
  have hNorm : 0 < ‖((2 : ℝ)^(-i)) • p‖ := (by norm_num : (0 : ℝ) < 1/2).trans_le H.1.1
  have hp : 0 < signedAxis sign (((2 : ℝ)^(-i)) • p) := (mul_pos hα hNorm).trans_le H.2
  rw [signedAxis_smul] at hp
  exact pos_of_mul_pos_right hp (by positivity)

/-- The four actual signed cap charts give the box profiles for the low
ratio remainder, using only one-sided C100 data. The result is the
geometric tail estimate for the original Fourier form with the same
three factors and actual dyadic annuli. -/
theorem exists_actual_cap_dyadic_remainder_tail_bound
    (B tube outer enlarged b : ℝ) (hB : 0 < B) (hTube : 0 < tube)
    (hOut : 0 ≤ outer) (hOE : outer < enlarged) (hb : 0 < b)
    (χ₀ : ℝ → ℝ) (oneχ₀ : χ₀ 0 = 1) (plateau : ∀ ρ ∈ Ioo (0 : ℝ) b, χ₀ ρ = 1) :
    ∃ (R : ℝ) (cutoff : ℕ) (C : ℝ), 0 < R ∧ R < 1 ∧ 4 ≤ cutoff ∧ 0 ≤ C ∧
      ∀ (metric : Form) (w : Vec) (F : NullCapChart metric w),
      ‖w‖ = 1 → ‖F.toFrequency.toContinuousLinearMap‖ ≤ B →
      ‖F.toFrequency.symm.toContinuousLinearMap‖ ≤ B →
      ∀ (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 → 4 * B * (5 * δ) ≤ 1 →
      let A := capFrequencyEquiv F hδ.ne'
      let Kplus := tsupport (enlargedCapMultiplier metric δ (tube*δ^2) outer enlarged w)
      let U := ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R
      let W := U ×ˢ Ico (0 : ℝ) b
      ∀ (M : CapSigns → LowRatio.Point → ℂ) (A₁₀₀ : ℝ), 0 ≤ A₁₀₀ →
      (∀ signs, ContDiffOn ℝ 100 (M signs) W) →
      (∀ signs n, n ≤ 100 → ∀ z ∈ W, ‖iteratedFDerivWithin ℝ n (M signs) W z‖ ≤ A₁₀₀) →
      ∀ (m : Joint → ℂ) (f g h : SchwartzMap E ℂ),
      (∀ p, radianWeight (fun _ => 1) f g h p ≠ 0 → A p.1 ∈ Kplus ∧ A p.2 ∈ Kplus) →
      (∀ signs (p : Joint), radianWeight (fun _ => 1) f g h p ≠ 0 →
        0 < signedAxis signs.1 p.1 → 0 < signedAxis signs.2 p.2 →
        let ρ := ‖A p.1‖ / ‖A p.2‖
        ρ ∈ Ioo (0 : ℝ) b → m p = ρ • LowRatio.remainder (M signs) χ₀
          ((endpointTail (endpointDirection p.1), endpointTail (endpointDirection p.2)), ρ)) →
      let T (s : {s : ℕ // cutoff ≤ s}) := radianTrilinearForm (radianLowGapSymbol m s.val) f g h
      let Mass := (triLpMass f g h 3 3 3).toReal
      (∀ s, ‖T s‖ ≤ C * A₁₀₀ * radialGapDecay s.val * Mass) ∧
      Summable (fun s => ‖T s‖) ∧
      ‖∑' s, T s‖ ≤ C * A₁₀₀ * (2 * radialGapDecay cutoff) * Mass := by
  obtain ⟨α,r,R,hα,hαOne,hr,hrR,hR,hCharts,hCover⟩ :=
    exists_actual_cap_signed_annular_boxes B tube outer enlarged hB hTube hOut hOE
  have hRpos : 0 < R := hr.trans hrR
  let U := ball (0 : EndpointAngle) R ×ˢ ball (0 : EndpointAngle) R
  have hU : IsOpen U := isOpen_ball.prod isOpen_ball
  have hPerChart (signs : CapSigns) := exists_actual_cap_positive_box_extension B tube outer enlarged
    (α/2) (1/4) 3 hB hTube hOut hOE (half_pos hα) (by norm_num)
    (hCharts signs).1 (hCharts signs).2.1 (hCharts signs).2.2.1 (hCharts signs).2.2.2.1 hU
    endpointTail endpointTail (hCharts signs).2.2.2.2 hb χ₀ oneχ₀ plateau
  choose D g₀ hD hChart using hPerChart
  let cutoff : ℕ := 4 + ∑ signs : CapSigns, g₀ signs
  have hc0 : 4 ≤ cutoff := by unfold cutoff; omega
  have hc (signs : CapSigns) : g₀ signs ≤ cutoff := by
    have H : g₀ signs ≤ ∑ e : CapSigns, g₀ e :=
      Finset.single_le_sum (f := g₀) (fun e _ => Nat.zero_le (g₀ e)) (Finset.mem_univ signs)
    unfold cutoff
    omega
  obtain ⟨Cbox,hCbox,hBox⟩ := exists_radianTrilinearForm_dyadic_remainder_tail_bound 5 (by norm_num)
  let C := Cbox * ∑ signs : CapSigns, D signs
  have hC : 0 ≤ C := mul_nonneg hCbox (Finset.sum_nonneg (fun signs _ => hD signs))
  refine ⟨R,cutoff,C,hRpos,hR,hc0,hC,?_⟩
  intro metric w F hw hFW hFI δ hδ hδOne hδSmall A Kplus U' W M A₁₀₀ hA₁₀₀ hSmooth hBound m f g h hSupp hSymbol T Mass
  have hData (signs : CapSigns) :=
    hChart signs metric w F hw hFW hFI δ hδ hδOne hδSmall (M signs) A₁₀₀ hA₁₀₀ (hSmooth signs) (hBound signs)
  choose G hGSmooth hGZero hGJet hGPos hGEq using hData
  let Gsum (s : ℕ) (z : BoxSpace) := ∑ signs : CapSigns, G signs s z
  obtain ⟨hSumSmooth,hSumJet,hSumEq⟩ :=
    signed_annular_box_profiles_sum hα G (fun signs => D signs * A₁₀₀) hGSmooth hGJet hGZero
  let budget := (∑ signs : CapSigns, D signs) * A₁₀₀
  have hBudget : 0 ≤ budget :=
    mul_nonneg (Finset.sum_nonneg (fun signs _ => hD signs)) hA₁₀₀
  have hJet (s n : ℕ) (hn : n ≤ 40) (z : BoxSpace) :
      ‖iteratedFDeriv ℝ n (Gsum s) z‖ ≤ budget * radialGapDecay s := by
    simpa only [Gsum, budget, Finset.sum_mul] using hSumJet s n hn z
  have hMatch (s : ℕ) (hs : cutoff ≤ s) (j : ℤ) (p : Joint) (hp : radianWeight (fun _ => 1) f g h p ≠ 0)
      (hlo : integerRadialWindow (j - (s : ℤ)) p.1 ≠ 0) (hhi : integerRadialWindow j p.2 ≠ 0) :
      Gsum s (joinedInputs (((2 : ℝ)^(-(j - (s : ℤ)))) • p.1) (((2 : ℝ)^(-j)) • p.2)) = m p := by
    let ζ := ((2 : ℝ)^(-(j - (s : ℤ)))) • p.1
    let υ := ((2 : ℝ)^(-j)) • p.2
    let z := joinedInputs ζ υ
    obtain ⟨signs, hKz, _⟩ := hCover metric w F hw hFI δ hδ hδSmall
      (j - (s : ℤ)) j p.1 p.2 hlo hhi (hSupp p hp).1 (hSupp p hp).2
    change boxToPair z ∈ signedPairK α signs at hKz
    have hK : (ζ,υ) ∈ signedPairK α signs := by simpa only [z,boxToPair_joined] using hKz
    have hS0 : g₀ signs ≤ s := (hc signs).trans hs
    have hV := (hCharts signs).2.2.1 hK
    have hρ := hGPos signs s hS0 (ζ,υ) hV
    have hq : p.2 ≠ 0 := by
      intro e
      apply hhi
      rw [e, integerRadialWindow_zero]
    have hυ : υ ≠ 0 := smul_ne_zero (by positivity) hq
    have restore (i : ℤ) (x : Frequency) : ((2 : ℝ)^i) • (((2 : ℝ)^(-i)) • x) = x := by
      rw [smul_smul, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero, one_smul]
    change gapRatio A s ζ υ ∈ Ioo (0 : ℝ) b at hρ
    rw [gapRatio_eq_physical A j s ζ υ hυ] at hρ
    dsimp only [ζ,υ] at hρ
    rw [restore,restore] at hρ
    have hSign1 : 0 < signedAxis signs.1 p.1 := signedAxis_pos_of_normalized hα p.1 _ signs.1 hK.1
    have hSign2 : 0 < signedAxis signs.2 p.2 := signedAxis_pos_of_normalized hα p.2 _ signs.2 hK.2
    change Gsum s z = m p
    exact (hSumEq signs s z hKz).trans ((hGEq signs s hS0 ζ υ hK).trans
      ((actual_signed_box_remainder_at_dyadic A M χ₀ signs j s p.1 p.2 hq).trans
        (hSymbol signs p hp hSign1 hSign2 hρ).symm))
  have H := hBox cutoff hc0 m Gsum budget hBudget
    (fun s => (hSumSmooth s).contDiffOn) (fun s n hn z _ => hJet s n hn z) f g h hMatch
  simpa only [C,budget,mul_assoc,mul_left_comm,mul_comm] using H

end Burnett.A05.BoxFourier
