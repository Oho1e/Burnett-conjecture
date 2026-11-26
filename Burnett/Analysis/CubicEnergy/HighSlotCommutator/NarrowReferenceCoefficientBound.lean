import Burnett.Analysis.CubicEnergy.HighSlotCommutator.NarrowReferenceWindows
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.CoefficientRadianBandSummation
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapRadian
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighSlotLowCoefficientInputs
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableReferenceRescaling

set_option autoImplicit false
set_option maxHeartbeats 7000000
noncomputable section
namespace Burnett.A06

open MeasureTheory Finset
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff BigOperators

private theorem high_coefficient_ratio_le (k : ℕ) (hk : 10≤k) :
    dyadicCoefficientScale 128 (k+1) ≤ 1/16 := by
  have hp : (2:ℝ)^11 ≤ (2:ℝ)^(k+1) :=
    pow_le_pow_right₀ (by norm_num) (Nat.succ_le_succ hk)
  unfold dyadicCoefficientScale
  calc
    _ ≤ (128:ℝ)/(2:ℝ)^11 := div_le_div_of_nonneg_left (by norm_num) (by positivity) hp
    _ = _ := by norm_num

/-- All coefficient scales are summed for the genuine reference multiplier
on a fixed narrow high-input ring. The constant is independent of the base
scale, the number of operator scales, and the particular Lipschitz coefficient. -/
theorem exists_narrowReference_unfilteredCoefficient_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (hBand : ∀ p : Joint, A p ≠ 0 → 1 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 5/4 ∧ ‖p.1‖ ≤ (1/2)*‖p.2‖) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (f g h : SchwartzMap E ℂ),
      ‖referenceUnfilteredCoefficientPairSum A D f g h t (range n)‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨χ,hχc,hχ₁,hχ₀,_⟩ := exists_coefficientRadialProfile (5/4) (7/4) (by norm_num) (by norm_num)
  obtain ⟨q,hqc,hqAnn,hq⟩ := exists_narrowReference_annulus
  let ψ := coefficientDyadicBandpass χ
  have hψc : HasCompactSupport (ψ : E → ℂ) := coefficientDyadicBandpass_compact χ hχc
  have hψBand := narrowDyadicBandpass_support χ hχ₁ hχ₀
  have hψAnn : ∀ ξ, ψ ξ ≠ 0 → 1/2<‖ξ‖ ∧ ‖ξ‖<2 :=
    coefficientDyadicBandpass_annulus χ (by norm_num) (by norm_num) hχ₁ hχ₀
  have hχ0 : χ 0=1 := hχ₁ 0 (by norm_num)
  have lowPlateau (z : E) (hz : ‖z‖≤(1/2)*(5/4)) : χ ((1:ℝ) • z)=1 := by
    rw [one_smul]
    exact hχ₁ z (by linarith only [hz])
  have inPlateau (z : E) (hl : 1-(7/512 : ℝ)≤‖z‖) (hu : ‖z‖≤5/4+7/512) :
      q ((1:ℝ) • z)=1 := by
    rw [one_smul]
    exact hq z (by linarith only [hl]) (by linarith only [hu])
  have outPlateau (z : E) (hl : (1-1/2)*1-(7/512 : ℝ)≤‖z‖)
      (hu : ‖z‖≤(1+1/2)*(5/4)+7/512) : q ((21/20 : ℝ) • z)=1 := by
    apply hq
    · rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤21/20)]
      linarith only [hl]
    · rw [norm_smul,Real.norm_of_nonneg (by norm_num : (0:ℝ)≤21/20)]
      linarith only [hu]
  have inStrong (z : E) (hl : 1≤‖z‖) (hu : ‖z‖≤5/4) : q ((1:ℝ) • z)=1 :=
    inPlateau z (by linarith only [hl]) (by linarith only [hu])
  have outStrong (z : E) (hl : (1-1/2)*1≤‖z‖) (hu : ‖z‖≤(1+1/2)*(5/4)) :
      q ((21/20 : ℝ) • z)=1 := outPlateau z (by linarith only [hl]) (by linarith only [hu])
  have topStrong (z : E)
      (hl : (5/8 : ℝ)-(1/16)*(1+1/2)*(5/4)≤‖z‖)
      (hu : ‖z‖≤(7/4 : ℝ)+(1/16)*(1+1/2)*(5/4)) : q ((1:ℝ) • z)=1 := by
    rw [one_smul]
    exact hq z (by linarith only [hl]) (by linarith only [hu])
  obtain ⟨ML,hML,lowBound⟩ := exists_lowpassCoefficientRadianBlocks_sum_bound_paper inputL2 A ha hA
    (lo := 1) (hi := 5/4) (ρ := 1/2) (ε := 7/512)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hBand
    q q χ (narrowLowCoefficientProfile χ) (narrowLowCoefficientProfile_support χ hχ₀)
    hqc hqc hqAnn hqAnn (u := 1) (v := 1) (w := 21/20)
    (by norm_num) (by norm_num) (by norm_num) lowPlateau inPlateau outPlateau
  obtain ⟨MH,hMH,highBound⟩ := exists_highCoefficientGap_radian_sum_bound_paper inputL2 A ha hA
    (lo := 1) (hi := 5/4) (ρ := 1/2) (ac := 5/8) (bc := 7/4) (r₀ := 1/16)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hBand q q q χ ψ
    (u := 1) (v := 1) (w := 21/20) (l := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    hqc hqc hqc hqAnn hqAnn hqAnn topStrong inStrong outStrong lowPlateau hψBand
  have fixedRatio (r : ℝ) (hr : 0<r) :
      ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
        ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (f g h : SchwartzMap E ℂ),
        (∑ j ∈ J, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
          (fun x => (windowTest ψ D (r*dyadicScale t j) x).re) f g h‖ₑ) ≤
          (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
    let S := (2:ℝ)+(1+1/2)*(r*(5/4))
    have hS : 0<S := by dsimp only [S]; positivity
    have scale (q : ℝ) : r⁻¹*(r*q) = q := by rw [← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
    have scl (q : ℝ) : (21/20/r)*(r*q) = (21/20)*q := by
      rw [div_eq_mul_inv,mul_assoc,scale]
    have shifted (z : E) (hz : ‖z‖≤S) : χ (S⁻¹ • z)=1 := by
      apply hχ₁
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hS.le)]
      exact ((mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hS.le)).trans_eq
        (inv_mul_cancel₀ hS.ne')).trans (by norm_num)
    have input (z : E) (hlo : r*1≤‖z‖) (hhi : ‖z‖≤r*(5/4)) : q (r⁻¹ • z)=1 := by
      have h₁ : 1≤‖r⁻¹ • z‖ := by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact (scale 1).symm.le.trans (mul_le_mul_of_nonneg_left hlo (inv_nonneg.mpr hr.le))
      have h₂ : ‖r⁻¹ • z‖≤5/4 := by
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
        exact (mul_le_mul_of_nonneg_left hhi (inv_nonneg.mpr hr.le)).trans_eq (scale (5/4))
      simpa only [one_smul] using inStrong _ h₁ h₂
    have output (z : E) (hlo : (1-1/2)*(r*1)≤‖z‖) (hhi : ‖z‖≤(1+1/2)*(r*(5/4))) :
        q ((21/20/r : ℝ) • z)=1 := by
      apply hq
      · rw [norm_smul,Real.norm_of_nonneg (by positivity : (0:ℝ)≤21/20/r)]
        have hh := mul_le_mul_of_nonneg_left hlo (by positivity : (0:ℝ)≤21/20/r)
        rw [show (1-1/2)*(r*1) = r*((1-1/2)*1) by ring,scl] at hh
        linarith only [hh]
      · rw [norm_smul,Real.norm_of_nonneg (by positivity : (0:ℝ)≤21/20/r)]
        have hh := mul_le_mul_of_nonneg_left hhi (by positivity : (0:ℝ)≤21/20/r)
        rw [show (1+1/2)*(r*(5/4)) = r*((1+1/2)*(5/4)) by ring,scl] at hh
        linarith only [hh]
    have low (z : E) (hz : ‖z‖≤(1/2)*(r*(5/4))) : χ (r⁻¹ • z)=1 := by
      apply hχ₁
      rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le)]
      have hh := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr hr.le)
      rw [show (1/2)*(r*(5/4)) = r*((1/2)*(5/4)) by ring,scale] at hh
      linarith only [hh]
    exact exists_comparableCoefficient_radian_sum_bound_of_ratio_paper inputL2 A ha hA hr (by norm_num) (by norm_num)
      hBand χ q q χ ψ (u := S⁻¹) (v := r⁻¹) (w := 21/20/r) (l := r⁻¹)
      (inv_pos.mpr hS) (inv_pos.mpr hr) (by positivity) (inv_pos.mpr hr)
      hψc hqc hqc hψAnn hqAnn hqAnn shifted input output low
  have hr (m : ℕ) : 0<dyadicCoefficientScale 128 (m+1) := dyadicCoefficientScale_pos (by norm_num) _
  choose MC hMC compBound using fun m : ℕ => fixedRatio (dyadicCoefficientScale 128 (m+1)) (hr m)
  let M := ML+(∑ m ∈ range 10, MC m)+MH*(2*ENNReal.ofReal 128)
  have hM : M<⊤ := ENNReal.add_lt_top.mpr
    ⟨ENNReal.add_lt_top.mpr ⟨hML,ENNReal.sum_lt_top.mpr fun m _ => hMC m⟩,
      ENNReal.mul_lt_top hMH (by finiteness)⟩
  refine ⟨M,hM,?_⟩
  intro D L hD t ht n f g h
  let mass := (L : ℝ≥0∞)*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2)
  have hLow : ‖referenceCoefficientWindowPairSum A χ D f g h t 128 (range n)‖ₑ ≤ ML*mass := by
    unfold referenceCoefficientWindowPairSum
    rw [← Fin.sum_univ_eq_sum_range]
    have h := lowBound ht n L D hD f g h
    simp only [narrowLowCoefficientProfile_window] at h
    exact h.trans_eq (by unfold mass; ring)
  have hComp (m : ℕ) (_hm : m<10) :
      ‖referenceCoefficientWindowPairSum A ψ D f g h t (dyadicCoefficientScale 128 (m+1)) (range n)‖ₑ
        ≤ MC m*mass := by
    unfold referenceCoefficientWindowPairSum
    exact (enorm_sum_le _ _).trans ((compBound m D L hD ht (range n) f g h).trans_eq
      (by unfold mass; ring))
  have hHigher (m : ℕ) (hm : 10≤m) :
      ‖referenceCoefficientWindowPairSum A ψ D f g h t (dyadicCoefficientScale 128 (m+1)) (range n)‖ₑ
        ≤ (MH*ENNReal.ofReal (dyadicCoefficientScale 128 (m+1)))*mass := by
    unfold referenceCoefficientWindowPairSum
    rw [← Fin.sum_univ_eq_sum_range]
    exact (enorm_sum_le _ _).trans
      ((highBound (hr m) (high_coefficient_ratio_le m hm) ht n L D hD f g h).trans_eq
        (by unfold mass; ring))
  exact (referenceUnfilteredCoefficientPairSum_bound_of_branches A ha hA χ D f g h hχ0 t 128
    (by norm_num) (range n) 10 ML MH mass MC hLow hComp hHigher).trans_eq
    (by unfold M mass; ring)

theorem exists_narrowReference_unfilteredCoefficient_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    (hBand : ∀ p : Joint, A p ≠ 0 → 1 ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ 5/4 ∧ ‖p.1‖ ≤ (1/2)*‖p.2‖) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (n : ℕ) (f g h : SchwartzMap E ℂ),
      ‖referenceUnfilteredCoefficientPairSum A D f g h t (range n)‖ₑ ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_narrowReference_unfilteredCoefficient_bound_paper false A ha hA hBand

end Burnett.A06
