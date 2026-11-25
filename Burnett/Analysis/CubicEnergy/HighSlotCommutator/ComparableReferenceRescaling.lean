import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableCoefficientRadian

set_option autoImplicit false
set_option maxHeartbeats 3250000
noncomputable section
namespace Burnett.A06

open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff BigOperators

private def comparableReferenceRescale (r : ℝ) (A : Joint → ℂ) (p : Joint) : ℂ :=
  r • A (r⁻¹ • p)

private theorem comparableReferenceRescale_regular {r : ℝ} (hr : 0<r) (A : Joint → ℂ)
    (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A) :
    HasCompactSupport (comparableReferenceRescale r A) ∧ ContDiff ℝ ∞ (comparableReferenceRescale r A) := by
  let F := (LinearEquiv.smulOfNeZero (K := ℝ) (M := Joint) r⁻¹ (inv_ne_zero hr.ne')).toContinuousLinearEquiv
  exact ⟨(ha.comp_homeomorph F.toHomeomorph).comp_left (smul_zero r : r • (0:ℂ) = 0),
    contDiff_const.smul (hA.comp F.contDiff)⟩

private theorem comparableReferenceRescale_band {r lo hi ρ : ℝ} (hr : 0<r) (A : Joint → ℂ)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖) :
    ∀ p : Joint, comparableReferenceRescale r A p ≠ 0 →
      r*lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ r*hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖ := by
  intro p hp
  have p' : A (r⁻¹ • p) ≠ 0 := by
    intro hz
    apply hp
    simp only [comparableReferenceRescale,hz,smul_zero]
  obtain ⟨hlo,hhi,hρ⟩ := hBand (r⁻¹ • p) p'
  simp only [Prod.smul_fst,Prod.smul_snd,norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),
    inv_mul_eq_div] at hlo hhi hρ
  have hρ' : ‖p.1‖/r ≤ (ρ*‖p.2‖)/r := by simpa only [← mul_div_assoc] using hρ
  exact ⟨by simpa only [mul_comm r lo] using (le_div_iff₀ hr).mp hlo,
    by simpa only [mul_comm r hi] using (div_le_iff₀ hr).mp hhi, (div_le_div_iff_of_pos_right hr).mp hρ'⟩

private theorem comparableReferenceRescale_radian {r : ℝ} (hr : 0<r)
    (A : Joint → ℂ) (s : ℝ) :
    radianHighReferenceBlock (comparableReferenceRescale r A) (r*s) = radianHighReferenceBlock A s := by
  funext p
  unfold radianHighReferenceBlock comparableReferenceRescale
  rw [smul_smul,smul_smul]
  have h₁ : r⁻¹*(r*s/tau) = s/tau := by
    rw [← mul_div_assoc,← mul_assoc,inv_mul_cancel₀ hr.ne',one_mul]
  have h₂ : (r*s)⁻¹*r = s⁻¹ := by rw [mul_inv_rev,mul_assoc,inv_mul_cancel₀ hr.ne',mul_one]
  rw [h₁,h₂]

/-- A fixed relative coefficient scale is handled by exactly the same
radian reference multiplier, using the transformed annular symbol. -/
theorem exists_comparableCoefficient_radian_sum_bound_of_ratio_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {r lo hi ρ : ℝ} (hr : 0<r) (hρ : 0≤ρ) (hρ' : ρ<1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (hprofile : HasCompactSupport (profile : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hProfileAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hShift : ∀ z : E, ‖z‖ ≤ 2+(1+ρ)*(r*hi) → a (u • z) = 1)
    (hIn : ∀ z : E, r*lo ≤ ‖z‖ → ‖z‖ ≤ r*hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*(r*lo) ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*(r*hi) → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*(r*hi) → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (f g h : SchwartzMap E ℂ),
      (∑ j ∈ J, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
        (fun x => (windowTest profile D (r*dyadicScale t j) x).re) f g h‖ₑ) ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨hc,hd⟩ := comparableReferenceRescale_regular hr A ha hA
  obtain ⟨M,hM,bound⟩ := exists_comparableCoefficient_radian_sum_bound_paper inputL2
    (comparableReferenceRescale r A) hc hd hρ hρ' (comparableReferenceRescale_band hr A hBand)
    a b e d profile hu hv hw hl hprofile hb he hProfileAnn hAnnB hAnnE hShift hIn hOut hLow
  refine ⟨M,hM,?_⟩
  intro D L hD t ht J f g h
  have scale (j : ℕ) : dyadicScale (r*t) j = r*dyadicScale t j := by unfold dyadicScale; ring
  simpa only [scale,comparableReferenceRescale_radian hr A] using bound D L hD (mul_pos hr ht) J f g h

theorem exists_comparableCoefficient_radian_sum_bound_of_ratio
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {r lo hi ρ : ℝ} (hr : 0<r) (hρ : 0≤ρ) (hρ' : ρ<1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (hprofile : HasCompactSupport (profile : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hProfileAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hShift : ∀ z : E, ‖z‖ ≤ 2+(1+ρ)*(r*hi) → a (u • z) = 1)
    (hIn : ∀ z : E, r*lo ≤ ‖z‖ → ‖z‖ ≤ r*hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*(r*lo) ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*(r*hi) → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*(r*hi) → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (f g h : SchwartzMap E ℂ),
      (∑ j ∈ J, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
        (fun x => (windowTest profile D (r*dyadicScale t j) x).re) f g h‖ₑ) ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_comparableCoefficient_radian_sum_bound_of_ratio_paper false A ha hA hr hρ hρ' hBand a b e d profile hu hv hw hl
    hprofile hb he hProfileAnn hAnnB hAnnE hShift hIn hOut hLow

end Burnett.A06
