import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighAnnularCoefficient
import Burnett.Analysis.CubicEnergy.HighSlotCommutator.HighCoefficientGapActual

set_option autoImplicit false
set_option maxHeartbeats 4450000
noncomputable section
namespace Burnett.A06

open MeasureTheory
open Burnett.A02.FrequencySplit
open scoped ENNReal NNReal ContDiff FourierTransform ComplexConjugate BigOperators

private theorem gapRadianPair_eq_tested {A : Joint → ℂ} (ha : HasCompactSupport A)
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

private theorem gapRadianCommutator_eq_tested {A : Joint → ℂ} (ha : HasCompactSupport A)
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
  rw [← eq g,← eq h,gapRadianPair_eq_tested ha hA,gapRadianPair_eq_tested ha hA,adjoint,smul_sub]

private theorem gapConjugate_triMass (inputL2 : Bool) (f g h : SchwartzMap E ℂ) :
    triLpMass f g (gapConjugate h) 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) = triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  have e : eLpNorm (gapConjugate h : E → ℂ) (ENNReal.ofReal (highSlotTestExponent inputL2)) volume =
      eLpNorm (h : E → ℂ) (ENNReal.ofReal (highSlotTestExponent inputL2)) volume :=
    eLpNorm_congr_norm_ae (.of_forall fun x => Complex.norm_conj (h x))
  unfold triLpMass
  rw [e]

/-- At each sufficiently separated higher coefficient band, the actual real
annular part of the same coefficient gives a radian commutator estimate.
The uniform constant precedes the separation ratio and every scale truncation. -/
theorem exists_highCoefficientGap_radian_sum_bound_paper
    (inputL2 : Bool)
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ac bc r₀ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hac : 0<ac)
    (hgap : r₀*(1+ρ)*hi < ac)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (ha' : HasCompactSupport (a : E → ℂ))
    (hb' : HasCompactSupport (b : E → ℂ))
    (he' : HasCompactSupport (e : E → ℂ))
    (hAnnA : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hTop : ∀ z : E, ac-r₀*(1+ρ)*hi ≤ ‖z‖ → ‖z‖ ≤ bc+r₀*(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1)
    (hProfile : ∀ z : E, profile z ≠ 0 → ac ≤ ‖z‖ ∧ ‖z‖ ≤ bc) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {r t : ℝ}, 0<r → r≤r₀ → 0<t →
      ∀ (n : ℕ) (L : ℝ≥0) (D : SchwartzMap E ℂ), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      (∑ i : Fin n, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t i))
        (fun x => (windowTest profile D (r*dyadicScale t i) x).re) f g h‖ₑ) ≤
        (L : ℝ≥0∞)*ENNReal.ofReal r*M*triLpMass f g h 4 (highSlotInputExponent inputL2) (highSlotTestExponent inputL2) := by
  obtain ⟨B,hB,bound⟩ := exists_highCoefficientGap_tested_sum_bound_paper inputL2 A ha hA hρ hρ' hgap hBand
    a b e d hu hv hw hl ha' hb' he' hAnnA hAnnB hAnnE hTop hIn hOut hLow
  refine ⟨(coefficientBandpassMoment profile : ℝ≥0∞)*B,ENNReal.mul_lt_top ENNReal.coe_lt_top hB,?_⟩
  intro r t hr hrr ht n L D hD f g h
  have hscale (i : Fin n) : 0 < r*dyadicScale t i := by unfold dyadicScale; positivity
  choose C hCReal hCAmpl hCFreq using fun i : Fin n =>
    exists_actual_spectralAnnularCoefficient profile D hac hProfile hD (hscale i)
  have ampl (i : Fin n) (x : E) :
      ‖C i x‖ ≤ ((coefficientBandpassMoment profile*L : ℝ≥0) : ℝ)*r*dyadicScale t i := by
    simpa only [mul_assoc] using hCAmpl i x
  simp_rw [fun i : Fin n => gapRadianCommutator_eq_tested ha hA (dyadicScale t i) _ (C i)
    f g h (hCReal i)]
  have hb := bound hr hrr ht n (coefficientBandpassMoment profile*L) C hCFreq ampl f g (gapConjugate h)
  rw [gapConjugate_triMass,ENNReal.coe_mul] at hb
  exact hb.trans_eq (by ac_rfl)

theorem exists_highCoefficientGap_radian_sum_bound
    (A : Joint → ℂ) (ha : HasCompactSupport A) (hA : ContDiff ℝ ∞ A)
    {lo hi ρ ac bc r₀ : ℝ} (hρ : 0 ≤ ρ) (hρ' : ρ < 1) (hac : 0<ac)
    (hgap : r₀*(1+ρ)*hi < ac)
    (hBand : ∀ p : Joint, A p ≠ 0 → lo ≤ ‖p.2‖ ∧ ‖p.2‖ ≤ hi ∧ ‖p.1‖ ≤ ρ*‖p.2‖)
    (a b e d profile : SchwartzMap E ℂ) {u v w l : ℝ} (hu : 0<u) (hv : 0<v) (hw : 0<w) (hl : 0<l)
    (ha' : HasCompactSupport (a : E → ℂ))
    (hb' : HasCompactSupport (b : E → ℂ))
    (he' : HasCompactSupport (e : E → ℂ))
    (hAnnA : ∀ ξ, a ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnB : ∀ ξ, b ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hAnnE : ∀ ξ, e ξ ≠ 0 → 1/2 < ‖ξ‖ ∧ ‖ξ‖ < 2)
    (hTop : ∀ z : E, ac-r₀*(1+ρ)*hi ≤ ‖z‖ → ‖z‖ ≤ bc+r₀*(1+ρ)*hi → a (u • z) = 1)
    (hIn : ∀ z : E, lo ≤ ‖z‖ → ‖z‖ ≤ hi → b (v • z) = 1)
    (hOut : ∀ z : E, (1-ρ)*lo ≤ ‖z‖ → ‖z‖ ≤ (1+ρ)*hi → e (w • z) = 1)
    (hLow : ∀ z : E, ‖z‖ ≤ ρ*hi → d (l • z) = 1)
    (hProfile : ∀ z : E, profile z ≠ 0 → ac ≤ ‖z‖ ∧ ‖z‖ ≤ bc) :
    ∃ M : ℝ≥0∞, M < ⊤ ∧ ∀ {r t : ℝ}, 0<r → r≤r₀ → 0<t →
      ∀ (n : ℕ) (L : ℝ≥0) (D : SchwartzMap E ℂ), LipschitzWith L D →
      ∀ f g h : SchwartzMap E ℂ,
      (∑ i : Fin n, ‖radianHighCommutatorPair (radianHighReferenceBlock A (dyadicScale t i))
        (fun x => (windowTest profile D (r*dyadicScale t i) x).re) f g h‖ₑ) ≤
        (L : ℝ≥0∞)*ENNReal.ofReal r*M*triLpMass f g h 4 4 2 :=
  exists_highCoefficientGap_radian_sum_bound_paper false A ha hA hρ hρ' hac hgap hBand
    a b e d profile hu hv hw hl ha' hb' he' hAnnA hAnnB hAnnE hTop hIn hOut hLow hProfile

end Burnett.A06
