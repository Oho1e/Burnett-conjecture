import Burnett.Analysis.CubicEnergy.HighSlotCommutator.ComparableTestedSum

set_option autoImplicit false
set_option maxHeartbeats 3900000
noncomputable section
namespace Burnett.A06

open MeasureTheory Finset
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff FourierTransform ComplexConjugate BigOperators

private theorem comparableRadianPair_eq_tested {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (f g h : SchwartzMap E ℂ) :
    radianHighPair (radianHighReferenceBlock A s) f g h =
      s⁻¹ • testedBlock A s f g (gapConjugate h) := by
  letI := jointVolume_haar
  have hτ : 0 < tau := mul_pos (by norm_num) Real.pi_pos
  have dimE : Module.finrank ℝ E = 4 := finrank_euclideanSpace_fin
  have dimJoint : Module.finrank ℝ Joint = 8 := by rw [Module.finrank_prod,dimE]
  have changeFreq := Measure.integral_comp_smul_of_nonneg (volume : Measure Joint)
    (radianHighPairWeight (radianHighReferenceBlock A s) f g h) tau (hR := hτ.le)
  rw [dimJoint] at changeFreq
  rw [radianHighPair,← changeFreq,testedBlock_density A ha hA,← integral_smul]
  apply integral_congr_ae
  filter_upwards with p
  have ratio : ((s/tau)*tau) = s := div_mul_cancel₀ _ hτ.ne'
  simp only [radianHighPairWeight,radianHighReferenceBlock,triDensity,smul_smul,ratio,
    Prod.smul_fst,Prod.smul_snd,← smul_add,add_comm p.2 p.1,gapConjugate_fourier,neg_neg,
    radianFourier_scaled,Complex.real_smul,mul_assoc]

private theorem comparableRadianCommutator_eq_tested {A : Joint → ℂ} (ha : HasCompactSupport A)
    (hA : ContDiff ℝ ∞ A) (s : ℝ) (c : E → ℝ) (C f g h : SchwartzMap E ℂ)
    (hc : ∀ x, C x = (c x : ℂ)) :
    radianHighCommutatorPair (radianHighReferenceBlock A s) c f g h =
      s⁻¹ • (testedBlock A s f (gapSchwartzProduct C g) (gapConjugate h) -
        testedBlock A s f g (gapSchwartzProduct C (gapConjugate h))) := by
  have eq (v : SchwartzMap E ℂ) :
      (gapSchwartzProduct C v : E → ℂ) = fun x => (c x : ℂ)*v x :=
    funext fun x => by rw [gapSchwartzProduct_apply,hc]
  have adjoint : gapConjugate (gapSchwartzProduct C h) = gapSchwartzProduct C (gapConjugate h) := by
    ext x
    change conj (gapSchwartzProduct C h x) = gapSchwartzProduct C (gapConjugate h) x
    simp only [gapSchwartzProduct_apply,map_mul,hc,Complex.conj_ofReal]
    rfl
  change radianHighPair (radianHighReferenceBlock A s) f (fun x => (c x : ℂ)*g x) h -
      radianHighPair (radianHighReferenceBlock A s) f g (fun x => (c x : ℂ)*h x) = _
  rw [← eq g,← eq h,comparableRadianPair_eq_tested ha hA,comparableRadianPair_eq_tested ha hA,adjoint,smul_sub]

private theorem comparableConjugate_mass (inputL2 : Bool) (f g h : SchwartzMap E ℂ) :
    triLpMass f g (gapConjugate h) 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) = triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  have e : eLpNorm (gapConjugate h : E → ℂ) (ENNReal.ofReal (highSlotTestExponent inputL2)) volume =
      eLpNorm (h : E → ℂ) (ENNReal.ofReal (highSlotTestExponent inputL2)) volume :=
    eLpNorm_congr_norm_ae (.of_forall fun x => Complex.norm_conj (h x))
  unfold triLpMass
  rw [e]

/-- The actual reference radian commutator with the real comparable-scale
coefficient annulus is summable uniformly in the finite choice of scales.
The high input and the high test use the two original exponent placements. -/
theorem exists_comparableCoefficient_radian_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (hprofile : HasCompactSupport (profile : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hProfileAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hShift : ∀ z : E, ‖z‖ ≤ 2+(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (f g h : SchwartzMap E ℂ),
      (∑ j ∈ J, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
        (fun x => (windowTest profile D (dyadicScale t j) x).re) f g h‖ₑ) ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨M,hM,bound⟩ := exists_comparableCoefficient_tested_sum_bound_paper inputL2 A ha hA hρ hρ' hBand
    a b e d profile hu hv hw hl hprofile hb he hProfileAnn hAnnB hAnnE hShift hIn hOut hLow
  refine ⟨M,hM,?_⟩
  intro D L hD t ht J f g h
  have hs (j : ℕ) : 0<dyadicScale t j := by unfold dyadicScale; positivity
  choose C hReal _ hf using fun j : ℕ => exists_actual_spectralAnnularCoefficient profile D
    (show (0:ℝ)<1/2 by norm_num) (fun z hz => ⟨(hProfileAnn z hz).1.le,(hProfileAnn z hz).2.le⟩) hD (hs j)
  have hFreq (j : ℕ) (z : E) (hz : 𝓕 (C j : E → ℂ) z ≠ 0) : ‖dyadicScale t j • z‖ ≤ 2 := (hf j z hz).2
  simp_rw [fun j : ℕ => comparableRadianCommutator_eq_tested ha hA (dyadicScale t j) _ (C j) f g h (hReal j)]
  simpa only [comparableConjugate_mass] using bound D L hD ht J C hReal hFreq f g (gapConjugate h)

theorem exists_comparableCoefficient_radian_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (hprofile : HasCompactSupport (profile : E → ℂ))
    (hb : HasCompactSupport (b : E → ℂ)) (he : HasCompactSupport (e : E → ℂ))
    (hProfileAnn : ∀ ξ, profile ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hShift : ∀ z : E, ‖z‖ ≤ 2+(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1) :
    ∃ M : ℝ≥0∞, M<⊤ ∧ ∀ (D : SchwartzMap E ℂ) (L : ℝ≥0), LipschitzWith L D →
      ∀ {t : ℝ}, 0<t → ∀ (J : Finset ℕ) (f g h : SchwartzMap E ℂ),
      (∑ j ∈ J, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t j))
        (fun x => (windowTest profile D (dyadicScale t j) x).re) f g h‖ₑ) ≤
        (L : ℝ≥0∞)*M*triLpMass f g h 4 4 2 :=
  exists_comparableCoefficient_radian_sum_bound_paper false A ha hA hρ hρ' hBand a b e d profile hu hv hw hl
    hprofile hb he hProfileAnn hAnnB hAnnE hShift hIn hOut hLow

end Burnett.A06
