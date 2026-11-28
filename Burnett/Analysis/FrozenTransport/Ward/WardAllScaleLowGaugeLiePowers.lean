import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers
import Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers

set_option autoImplicit false
set_option maxRecDepth 6200
set_option maxHeartbeats 12000000
noncomputable section

namespace Burnett.C02

open Set Metric Burnett.A05 Burnett.A02.FrequencySplit
open Burnett.RicciSymbol (Tensor2)
open Burnett.P01 (ComplexComponents ComplexCovector)
open Burnett.V08 (normalizedGaugePotential normalizedGaugePotential_contDiff cyclicLowNormalizedPhase
  cyclicLowNormalizedPhase_contDiffOn signedCyclicPhase signedCyclicPhase_div_eq_lowNormalized)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped ContDiff

open private raisedWardGaugeComponent raisedWardGaugeComponent_const_mul wardHighThirdVector wardHighThirdVector_ne_zero from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleHighGaugePowers
open private wardGaugePotentialAt from Burnett.Analysis.FrozenTransport.Ward.WardAllScaleTwoGaugePowers

private def wardLieVector (m : Tensor2) (J : ComplexComponents) (v : ComplexCovector) (b : Fin 4) : ℂ :=
  ∑ c : Fin 4, J c b * raisedWardGaugeComponent m v c

/-- The unsymmetrized action inputs are retained and only the insertion
`K_p(L(m⁻¹v,·))` supplies its two symmetric terms. -/
def wardLieGaugeInsertion (m : Tensor2) (J : ComplexComponents) (v : ComplexCovector) (p : E) :
    ComplexComponents :=
  fun a b => (p a : ℂ) * wardLieVector m J v b + (p b : ℂ) * wardLieVector m J v a

def wardScreenLieContraction (m : Tensor2) (H J : ComplexComponents) (v : ComplexCovector) (p : E) : ℂ :=
  frozenWardScreenPair m H (wardLieGaugeInsertion m J v p)

private theorem wardLieVector_scale (m : Tensor2) (J : ComplexComponents) (v : ComplexCovector)
    (t : ℝ) (b : Fin 4) : wardLieVector m J (fun c => (t : ℂ) * v c) b = (t : ℂ) * wardLieVector m J v b := by
  simp only [wardLieVector, raisedWardGaugeComponent_const_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro c _
  ring

private theorem wardScreenLieContraction_normalize (m : Tensor2) (H J : ComplexComponents)
    (p : E) (hp : p ≠ 0) (G : ComplexComponents) :
    wardScreenLieContraction m H J (wardGaugePotentialAt p G) p =
      wardScreenLieContraction m H J (normalizedGaugePotential (endpointDirection p) G) (endpointDirection p) := by
  let d := endpointDirection p
  let v := normalizedGaugePotential d G
  have hp₀ := norm_ne_zero_iff.mpr hp
  have hc : (‖p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp₀
  have he : ‖p‖ • d = p := smul_inv_smul₀ hp₀ p
  unfold wardScreenLieContraction
  congr 1
  have h (a b : Fin 4) :
      (p a : ℂ) * wardLieVector m J (wardGaugePotentialAt p G) b = (d a : ℂ) * wardLieVector m J v b := by
    have hpa : p a = ‖p‖ * d a := by
      exact congrArg (fun y : E => y a) he.symm
    rw [show wardGaugePotentialAt p G = (fun c => ((‖p‖⁻¹ : ℝ) : ℂ) * v c) from rfl,
      wardLieVector_scale, hpa]
    simp only [Complex.ofReal_mul, Complex.ofReal_inv]
    field_simp
  ext a b
  change _ * _ + _ * _ = _ * _ + _ * _
  rw [h a b, h b a]

private theorem wardScreenLieContraction_profile_smooth (m : Tensor2) (H J G : ComplexComponents) :
    ContDiff ℝ ∞ (fun dir : E => wardScreenLieContraction m H J (normalizedGaugePotential dir G) dir) := by
  have hG (b : Fin 4) : ContDiff ℝ ∞ (fun d : E => wardLieVector m J (normalizedGaugePotential d G) b) := by
    unfold wardLieVector raisedWardGaugeComponent
    exact ContDiff.sum fun c _ => contDiff_const.mul
      (ContDiff.sum fun j _ => contDiff_const.mul (normalizedGaugePotential_contDiff G j))
  have hD (i : Fin 4) : ContDiff ℝ ∞ (fun d : E => (d i : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
  have hK (a b : Fin 4) : ContDiff ℝ ∞ (fun d : E => wardLieGaugeInsertion m J (normalizedGaugePotential d G) d a b) :=
    ((hD a).mul (hG b)).add ((hD b).mul (hG a))
  unfold wardScreenLieContraction frozenWardScreenPair
  exact contDiff_const.mul (ContDiff.sum fun a _ => ContDiff.sum fun b _ =>
    ContDiff.sum fun i _ => ContDiff.sum fun j _ => contDiff_const.mul (hK a b))

/-- Smooth normalized symbols for the last two terms of line 2144–2145,
retaining the two original physical phases and all density factors. -/
def lowGaugeLiePhaseProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (x : WardLowPoint) : ℂ × ℂ :=
  let A := (-2 : ℂ) * (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ) * (w : ℂ)
  let V := normalizedGaugePotential x.1 G
  let R := (‖wardHighThirdVector x‖ : ℂ)
  (A * wardScreenLieContraction m H J V x.1 / R, A * wardScreenLieContraction m J H V x.1 * R)

theorem lowGaugeLiePhaseProfiles_contDiffOn (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G H J : ComplexComponents) :
    ContDiffOn ℝ ∞ (lowGaugeLiePhaseProfiles m w a G H J) wardLowProfileDomain := by
  have hC : ContDiffOn ℝ ∞ (fun x : WardLowPoint =>
      (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ)) wardLowProfileDomain := by
    apply (Complex.ofRealCLM.contDiff.comp_contDiffOn (cyclicLowNormalizedPhase_contDiffOn a ha)).comp
      (contDiff_fst.prodMk ((contDiff_snd.snd.smul contDiff_fst).prodMk contDiff_snd.fst)).contDiffOn
    exact fun _ hx => hx
  have hR : ContDiff ℝ ∞ wardHighThirdVector := (contDiff_snd.fst.add (contDiff_snd.snd.smul contDiff_fst)).neg
  have hN := Complex.ofRealCLM.contDiff.comp_contDiffOn (hR.contDiffOn.norm ℝ wardHighThirdVector_ne_zero)
  have hA := ((contDiffOn_const (c := (-2 : ℂ))).mul hC).mul (contDiffOn_const (c := (w : ℂ)))
  have hAq := hA.mul ((wardScreenLieContraction_profile_smooth m H J G).comp contDiff_fst).contDiffOn
  have hAr := hA.mul ((wardScreenLieContraction_profile_smooth m J H G).comp contDiff_fst).contDiffOn
  have hi := hN.inv (fun x hx => Complex.ofReal_ne_zero.mpr
    (norm_ne_zero_iff.mpr (wardHighThirdVector_ne_zero x hx)))
  simpa only [lowGaugeLiePhaseProfiles, div_eq_mul_inv] using (hAq.mul hi).prodMk (hAr.mul hN)

theorem lowGaugeLiePhase_eq_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) (hlow : ‖p‖ / ‖q‖ < 1 / 2)
    (G H J : ComplexComponents) :
    let r := -(p + q)
    let x : WardLowPoint := (endpointDirection p, endpointDirection q, ‖p‖ / ‖q‖)
    let v := wardGaugePotentialAt p G
    (-2 : ℂ) * (signedCyclicPhase a p q : ℂ) * (w : ℂ) *
        ((quadratic m q : ℂ) * wardScreenLieContraction m H J v p +
          (quadratic m r : ℂ) * wardScreenLieContraction m J H v p) /
        ((‖p‖ * ‖q‖ * ‖r‖ : ℝ) : ℂ) =
      (lowGaugeLiePhaseProfiles m w a G H J x).1 * (normalizedFrozenPhase m q : ℂ) +
        (lowGaugeLiePhaseProfiles m w a G H J x).2 * (normalizedFrozenPhase m r : ℂ) := by
  intro r x v
  have hp₀ := norm_pos_iff.mpr hp
  have hq₀ := norm_pos_iff.mpr hq
  have hP : ‖p‖ • x.1 = p := smul_inv_smul₀ hp₀.ne' p
  have hQ : ‖q‖ • x.2.1 = q := smul_inv_smul₀ hq₀.ne' q
  have hDirP : ‖x.1‖ = 1 := mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hp)
  have hDirQ : ‖x.2.1‖ = 1 := mem_sphere_zero_iff_norm.mp (endpointDirection_mem_sphere hq)
  have hZ : ‖x.2.2 • x.1‖ < 1 / 2 := by
    rw [norm_smul, hDirP, mul_one, Real.norm_of_nonneg (div_nonneg (norm_nonneg p) (norm_nonneg q))]
    exact hlow
  have hx : x ∈ wardLowProfileDomain := ⟨by rw [hDirP]; norm_num, hZ, by rw [hDirQ]; norm_num⟩
  have hR := wardHighThirdVector_ne_zero x hx
  have hr : r = ‖q‖ • wardHighThirdVector x := wardLowSignedThird_eq p q hp hq
  have hrNorm : ‖r‖ = ‖q‖ * ‖wardHighThirdVector x‖ := by
    conv_lhs => rw [hr, norm_smul, Real.norm_of_nonneg hq₀.le]
  have hr₀ : 0 < ‖r‖ := hrNorm.symm ▸ mul_pos hq₀ (norm_pos_iff.mpr hR)
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
  dsimp only [v]
  rw [hc, wardScreenLieContraction_normalize m H J p hp G, wardScreenLieContraction_normalize m J H p hp G,
    hPhase q hq₀, hPhase r hr₀, hrNorm]
  have hpC : (‖p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp₀.ne'
  have hqC : (‖q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have hRC : (‖wardHighThirdVector x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hR)
  have hd : endpointDirection p = x.1 := rfl
  simp only [lowGaugeLiePhaseProfiles, Complex.ofReal_mul, hd]
  field_simp
  ring

end Burnett.C02
