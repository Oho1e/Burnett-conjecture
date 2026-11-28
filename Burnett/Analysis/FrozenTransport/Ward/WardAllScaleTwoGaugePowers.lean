import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

set_option autoImplicit false
set_option maxRecDepth 6100
set_option maxHeartbeats 12200000
noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ComplexComponents ComplexCovector)
open Burnett.V08 (normalizedGaugePotential normalizedGaugePotential_contDiff cyclicLowNormalizedPhase
  cyclicLowNormalizedPhase_contDiffOn signedCyclicPhase signedCyclicPhase_div_eq_lowNormalized)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped ContDiff

open private raisedWardScreenEntry raisedWardGaugeComponent raisedWardGaugeComponent_const_mul wardHighThirdVector wardHighThirdVector_ne_zero from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

private def raisedScreenBilinear (m : Tensor2) (H : ComplexComponents) (p q : E) : ℂ :=
  ∑ a : Fin 4, ∑ b : Fin 4, raisedWardScreenEntry m H a b * (p a : ℂ) * (q b : ℂ)

/-- Transversality of the physical slot puts the other signed covector
in both factors of its raised quadratic contraction. -/
theorem raisedScreenBilinear_signedThird_self (m : Tensor2) (H : ComplexComponents)
    (p q : E) (h₁ : ∀ b, ∑ a : Fin 4, raisedWardScreenEntry m H a b * (q a : ℂ) = 0)
    (h₂ : ∀ a, ∑ b : Fin 4, raisedWardScreenEntry m H a b * (q b : ℂ) = 0) :
    raisedScreenBilinear m H (-(p + q)) (-(p + q)) = raisedScreenBilinear m H p p := by
  have ha (u : E) : raisedScreenBilinear m H q u = 0 := by
    unfold raisedScreenBilinear
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro b _
    rw [← Finset.sum_mul, h₁ b, zero_mul]
  have hb (u : E) : raisedScreenBilinear m H u q = 0 := by
    unfold raisedScreenBilinear
    apply Finset.sum_eq_zero
    intro a _
    simp_rw [mul_comm (raisedWardScreenEntry m H a _) (u a : ℂ), mul_assoc,
      ← Finset.mul_sum, h₂ a, mul_zero]
  have hExp : raisedScreenBilinear m H (-(p + q)) (-(p + q)) =
      raisedScreenBilinear m H p p + raisedScreenBilinear m H p q +
        (raisedScreenBilinear m H q p + raisedScreenBilinear m H q q) := by
    have hTerm (i j : Fin 4) :
        raisedWardScreenEntry m H i j * ((-(p+q)) i : ℂ) * ((-(p+q)) j : ℂ) =
          raisedWardScreenEntry m H i j * (p i : ℂ) * (p j : ℂ) +
          raisedWardScreenEntry m H i j * (p i : ℂ) * (q j : ℂ) +
          (raisedWardScreenEntry m H i j * (q i : ℂ) * (p j : ℂ) +
          raisedWardScreenEntry m H i j * (q i : ℂ) * (q j : ℂ)) := by
      simp only [PiLp.neg_apply, PiLp.add_apply, Complex.ofReal_neg, Complex.ofReal_add]
      ring
    simp only [raisedScreenBilinear, hTerm, Finset.sum_add_distrib]
  rw [hExp, ha p, ha q, hb p, add_zero, add_zero, add_zero]

private def wardTwoGaugePair (m : Tensor2) (u v : ComplexCovector) : ℂ :=
  ∑ c : Fin 4, u c * raisedWardGaugeComponent m v c

/-- The bilinear gauge-pair and raised screen contraction in the exact
two-gauge formula, with the physical phase still factored out. -/
def wardTwoGaugeBracket (m : Tensor2) (H : ComplexComponents) (u v : ComplexCovector) (p : E) : ℂ :=
  wardTwoGaugePair m u v * raisedScreenBilinear m H p p

private theorem wardTwoGaugePair_scale (m : Tensor2) (u v : ComplexCovector) (t s : ℝ) :
    wardTwoGaugePair m (fun j => (t : ℂ) * u j) (fun j => (s : ℂ) * v j) =
      ((t * s : ℝ) : ℂ) * wardTwoGaugePair m u v := by
  simp only [wardTwoGaugePair, raisedWardGaugeComponent_const_mul, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem raisedScreenBilinear_scale_self (m : Tensor2) (H : ComplexComponents) (d : E) (t : ℝ) :
    raisedScreenBilinear m H (t • d) (t • d) = (t : ℂ)^2 * raisedScreenBilinear m H d d := by
  simp only [raisedScreenBilinear, PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem wardTwoGaugeBracket_scale (m : Tensor2) (H : ComplexComponents) (u v : ComplexCovector)
    (p : E) (t s d : ℝ) :
    wardTwoGaugeBracket m H (fun j => (t : ℂ) * u j) (fun j => (s : ℂ) * v j) (d • p) =
      ((t * s * d^2 : ℝ) : ℂ) * wardTwoGaugeBracket m H u v p := by
  simp only [wardTwoGaugeBracket, wardTwoGaugePair_scale, raisedScreenBilinear_scale_self,
    Complex.ofReal_mul, Complex.ofReal_pow]
  ring

private theorem wardTwoGaugeBracket_smooth (m : Tensor2) (H : ComplexComponents)
    (u v : WardLowPoint → ComplexCovector) (d : WardLowPoint → E)
    (hu : ∀ i, ContDiffOn ℝ ∞ (fun x => u x i) wardLowProfileDomain)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => v x i) wardLowProfileDomain)
    (hd : ContDiffOn ℝ ∞ d wardLowProfileDomain) :
    ContDiffOn ℝ ∞ (fun x => wardTwoGaugeBracket m H (u x) (v x) (d x)) wardLowProfileDomain := by
  have hV (i : Fin 4) : ContDiffOn ℝ ∞ (fun x => raisedWardGaugeComponent m (v x) i) wardLowProfileDomain :=
    ContDiffOn.sum (fun j _ => (contDiffOn_const (c := (m i j : ℂ))).mul (hv j))
  have hD (i : Fin 4) : ContDiffOn ℝ ∞ (fun x => (d x i : ℂ)) wardLowProfileDomain :=
    (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp_contDiffOn hd
  exact (ContDiffOn.sum fun i _ => (hu i).mul (hV i)).mul
    (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j _ =>
      ((contDiffOn_const (c := raisedWardScreenEntry m H i j)).mul (hD i)).mul (hD j))

/-- Smooth extensions for the two-gauge term with either the physical slot
or the first gauge slot designated as the low slot. -/
def twoGaugePhaseProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G₁ G₂ H : ComplexComponents)
    (x : WardLowPoint) : ℂ × ℂ :=
  let R := wardHighThirdVector x
  let V := normalizedGaugePotential (endpointDirection R) G₂
  let C := (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ) * (w : ℂ) * (‖R‖ : ℂ)⁻¹ ^ 2
  (C * wardTwoGaugeBracket m H V (normalizedGaugePotential x.2.1 G₁) x.2.1,
    C * wardTwoGaugeBracket m H V (normalizedGaugePotential x.1 G₁) x.1)

theorem twoGaugePhaseProfiles_contDiffOn (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G₁ G₂ H : ComplexComponents) :
    ContDiffOn ℝ ∞ (twoGaugePhaseProfiles m w a G₁ G₂ H) wardLowProfileDomain := by
  have hC : ContDiffOn ℝ ∞ (fun x : WardLowPoint =>
      (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ)) wardLowProfileDomain := by
    apply (Complex.ofRealCLM.contDiff.comp_contDiffOn (cyclicLowNormalizedPhase_contDiffOn a ha)).comp
      (contDiff_fst.prodMk ((contDiff_snd.snd.smul contDiff_fst).prodMk contDiff_snd.fst)).contDiffOn
    exact fun _ hx => hx
  have hR : ContDiff ℝ ∞ wardHighThirdVector := (contDiff_snd.fst.add (contDiff_snd.snd.smul contDiff_fst)).neg
  have hDir := endpointDirection_contDiffOn.comp hR.contDiffOn wardHighThirdVector_ne_zero
  have hV (i : Fin 4) : ContDiffOn ℝ ∞
      (fun x : WardLowPoint => normalizedGaugePotential (endpointDirection (wardHighThirdVector x)) G₂ i)
        wardLowProfileDomain := (normalizedGaugePotential_contDiff G₂ i).comp_contDiffOn hDir
  have hP (i : Fin 4) : ContDiffOn ℝ ∞
      (fun x : WardLowPoint => normalizedGaugePotential x.1 G₁ i) wardLowProfileDomain :=
    ((normalizedGaugePotential_contDiff G₁ i).comp contDiff_fst).contDiffOn
  have hQ (i : Fin 4) : ContDiffOn ℝ ∞
      (fun x : WardLowPoint => normalizedGaugePotential x.2.1 G₁ i) wardLowProfileDomain :=
    ((normalizedGaugePotential_contDiff G₁ i).comp contDiff_snd.fst).contDiffOn
  have hRN := Complex.ofRealCLM.contDiff.comp_contDiffOn (hR.contDiffOn.norm ℝ wardHighThirdVector_ne_zero)
  have hInv := hRN.inv (fun x hx => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (wardHighThirdVector_ne_zero x hx)))
  have hC' := (hC.mul (contDiffOn_const (c := (w : ℂ)))).mul (hInv.pow 2)
  exact (hC'.mul (wardTwoGaugeBracket_smooth m H _ _ _ hV hQ contDiff_snd.fst.contDiffOn)).prodMk
    (hC'.mul (wardTwoGaugeBracket_smooth m H _ _ _ hV hP contDiff_fst.contDiffOn))

private def wardGaugePotentialAt (p : E) (G : ComplexComponents) : ComplexCovector :=
  fun j => (‖p‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection p) G j

/-- The paper's two double-gauge phase powers with the true signed third
frequency. Both use the phase of the designated physical slot. -/
theorem twoGaugePhase_eq_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) (hlow : ‖p‖ / ‖q‖ < 1 / 2)
    (G₁ G₂ H : ComplexComponents) :
    let r := -(p + q)
    let x : WardLowPoint := (endpointDirection p, endpointDirection q, ‖p‖ / ‖q‖)
    let T := (signedCyclicPhase a p q : ℂ) * (w : ℂ)
    let D := ((‖p‖ * ‖q‖ * ‖r‖ : ℝ) : ℂ)
    let U := wardGaugePotentialAt r G₂
    (T * (quadratic m p : ℂ) * wardTwoGaugeBracket m H U (wardGaugePotentialAt q G₁) q / D =
      (twoGaugePhaseProfiles m w a G₁ G₂ H x).1 * (x.2.2 : ℂ)^2 * (normalizedFrozenPhase m p : ℂ)) ∧
    (T * (quadratic m q : ℂ) * wardTwoGaugeBracket m H U (wardGaugePotentialAt p G₁) p / D =
      (twoGaugePhaseProfiles m w a G₁ G₂ H x).2 * (x.2.2 : ℂ) * (normalizedFrozenPhase m q : ℂ)) := by
  intro r x T D U
  have hp₀ := norm_pos_iff.mpr hp
  have hq₀ := norm_pos_iff.mpr hq
  have hP : ‖p‖ • x.1 = p := smul_inv_smul₀ hp₀.ne' p
  have hQ : ‖q‖ • x.2.1 = q := smul_inv_smul₀ hq₀.ne' q
  have hDirP : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp)
  have hDirQ : ‖x.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hq)
  have hZ : ‖x.2.2 • x.1‖ < 1 / 2 := by
    rw [norm_smul, hDirP, mul_one, Real.norm_of_nonneg (div_nonneg (norm_nonneg p) (norm_nonneg q))]
    exact hlow
  have hx : x ∈ wardLowProfileDomain := ⟨by rw [hDirP]; norm_num,hZ,by rw [hDirQ]; norm_num⟩
  have hR := wardHighThirdVector_ne_zero x hx
  have hr : r = ‖q‖ • wardHighThirdVector x := wardLowSignedThird_eq p q hp hq
  have hrNorm : ‖r‖ = ‖q‖ * ‖wardHighThirdVector x‖ := by
    conv_lhs => rw [hr, norm_smul, Real.norm_of_nonneg hq₀.le]
  have hrDir : endpointDirection r = endpointDirection (wardHighThirdVector x) := by
    rw [hr, endpointDirection_pos_smul ‖q‖ hq₀]
  let V := normalizedGaugePotential (endpointDirection (wardHighThirdVector x)) G₂
  have hU : U = fun i => (‖r‖⁻¹ : ℝ) * V i := by
    funext i
    change (‖r‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection r) G₂ i = _
    rw [hrDir]
  have hGauge (ξ : E) : (fun i => (‖ξ‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection ξ) G₁ i) =
      wardGaugePotentialAt ξ G₁ := rfl
  have hQBracket := wardTwoGaugeBracket_scale m H V (normalizedGaugePotential x.2.1 G₁) x.2.1 ‖r‖⁻¹ ‖q‖⁻¹ ‖q‖
  have hPBracket := wardTwoGaugeBracket_scale m H V (normalizedGaugePotential x.1 G₁) x.1 ‖r‖⁻¹ ‖p‖⁻¹ ‖p‖
  rw [hQ, ← hU, hGauge q] at hQBracket
  rw [hP, ← hU, hGauge p] at hPBracket
  have hC := signedCyclicPhase_div_eq_lowNormalized a ha hOdd hHom x.1 (x.2.2 • x.1) x.2.1
    ‖p‖ ‖q‖ hp₀ hq₀ hDirQ hZ rfl
  rw [hP, hQ] at hC
  have hc : (signedCyclicPhase a p q : ℂ) =
      (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ) * (‖p‖ : ℂ) := by
    exact_mod_cast (div_eq_iff hp₀.ne').mp hC
  have hPhase (k : E) (hk : 0 < ‖k‖) :
      (quadratic m k : ℂ) = (normalizedFrozenPhase m k : ℂ) * (‖k‖ : ℂ)^2 := by
    have hReal : quadratic m k = normalizedFrozenPhase m k * ‖k‖^2 :=
      (div_eq_iff (pow_ne_zero 2 hk.ne')).mp (show
        quadratic m k / ‖k‖^2 = normalizedFrozenPhase m k from rfl)
    exact_mod_cast hReal
  have Hp : (‖p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp₀.ne'
  have Hq : (‖q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have HR : (‖wardHighThirdVector x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hR)
  have hRatio : (x.2.2 : ℂ) = (‖p‖ : ℂ) / (‖q‖ : ℂ) := Complex.ofReal_div _ _
  constructor
  · dsimp only [T, D]
    rw [hc, hQBracket, hPhase p hp₀, hrNorm]
    simp only [twoGaugePhaseProfiles, hRatio, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
    dsimp only [V]
    field_simp
  · dsimp only [T, D]
    rw [hc, hPBracket, hPhase q hq₀, hrNorm]
    simp only [twoGaugePhaseProfiles, hRatio, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow]
    dsimp only [V]
    field_simp

end Burnett.C02
