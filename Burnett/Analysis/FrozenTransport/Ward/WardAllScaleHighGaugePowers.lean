import Burnett.Analysis.FrozenTransport.Ward.WardLowTransferCoordinates

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

private def raisedWardScreenEntry (m : Tensor2) (H : ComplexComponents) (a b : Fin 4) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (m a i : ℂ) * (m b j : ℂ) * H i j

private def raisedWardGaugeComponent (m : Tensor2) (v : ComplexCovector) (c : Fin 4) : ℂ :=
  ∑ j : Fin 4, (m c j : ℂ) * v j

/-- The coefficient of one physical phase in line 2198, without its
volume factor. The first summand is the transport contraction and the
second the contraction through the high gauge generator. -/
def wardHighGaugeBracket (m : Tensor2) (pair : ℂ) (H J : ComplexComponents)
    (v : ComplexCovector) (d : E) : ℂ :=
  -2 * (∑ i : Fin 4, raisedWardGaugeComponent m v i * (d i : ℂ)) * pair +
    ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4,
      raisedWardScreenEntry m H a b * (d a : ℂ) * J b c * raisedWardGaugeComponent m v c

private theorem raisedWardGaugeComponent_const_mul (m : Tensor2) (v : ComplexCovector) (t : ℝ) (c : Fin 4) :
    raisedWardGaugeComponent m (fun i => (t : ℂ) * v i) c = (t : ℂ) * raisedWardGaugeComponent m v c := by
  simp only [raisedWardGaugeComponent, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem wardHighGaugeBracket_scale (m : Tensor2) (pair : ℂ) (H J : ComplexComponents)
    (v : ComplexCovector) (d : E) (t s : ℝ) :
    wardHighGaugeBracket m pair H J (fun i => (t : ℂ) * v i) (s • d) =
      ((t * s : ℝ) : ℂ) * wardHighGaugeBracket m pair H J v d := by
  simp only [wardHighGaugeBracket, raisedWardGaugeComponent_const_mul, PiLp.smul_apply,
    smul_eq_mul, Complex.ofReal_mul, mul_add]
  congr 1
  · have h : (∑ i : Fin 4, (t : ℂ) * raisedWardGaugeComponent m v i * ((s : ℂ) * (d i : ℂ))) =
        ((t : ℂ) * (s : ℂ)) * ∑ i : Fin 4, raisedWardGaugeComponent m v i * (d i : ℂ) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [h]
    ring
  · simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring

private theorem wardHighGaugeBracket_smooth (m : Tensor2) (pair : ℂ) (H J : ComplexComponents)
    (v : WardLowPoint → ComplexCovector) (d : WardLowPoint → E)
    (hv : ∀ i, ContDiffOn ℝ ∞ (fun x => v x i) wardLowProfileDomain)
    (hd : ContDiffOn ℝ ∞ d wardLowProfileDomain) :
    ContDiffOn ℝ ∞ (fun x => wardHighGaugeBracket m pair H J (v x) (d x)) wardLowProfileDomain := by
  have hV (i : Fin 4) : ContDiffOn ℝ ∞ (fun x => raisedWardGaugeComponent m (v x) i) wardLowProfileDomain := by
    exact ContDiffOn.sum (fun j _ => (contDiffOn_const (c := (m i j : ℂ))).mul (hv j))
  have hD (i : Fin 4) : ContDiffOn ℝ ∞ (fun x => (d x i : ℂ)) wardLowProfileDomain :=
    (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff).comp_contDiffOn hd
  unfold wardHighGaugeBracket
  exact (((contDiffOn_const (c := (-2 : ℂ))).mul (ContDiffOn.sum (fun i _ => (hV i).mul (hD i)))).mul
    (contDiffOn_const (c := pair))).add (ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ =>
      ContDiffOn.sum fun c _ => (((contDiffOn_const (c := raisedWardScreenEntry m H a b)).mul (hD a)).mul
        (contDiffOn_const (c := J b c))).mul (hV c))

private def wardHighThirdVector (x : WardLowPoint) : E := -(x.2.1 + x.2.2 • x.1)

private theorem wardHighThirdVector_ne_zero (x : WardLowPoint) (hx : x ∈ wardLowProfileDomain) :
    wardHighThirdVector x ≠ 0 := by
  unfold wardHighThirdVector
  apply neg_ne_zero.mpr
  intro h
  have he := eq_neg_of_add_eq_zero_left h
  have hn := hx.2.2
  rw [he, norm_neg] at hn
  linarith only [hn, hx.2.1]

/-- The two coefficients are smooth through ratio zero. The ratio powers
are kept outside these profiles and on their designated physical phases. -/
def highGaugePhaseProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (x : WardLowPoint) : ℂ × ℂ :=
  let R := wardHighThirdVector x
  let V := normalizedGaugePotential (endpointDirection R) G
  let pair := frozenWardScreenPair m H J
  let C := (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ) * (w : ℂ) * (‖R‖ : ℂ)⁻¹ ^ 2
  (C * wardHighGaugeBracket m pair H J V x.2.1, C * wardHighGaugeBracket m pair J H V x.1)

theorem highGaugePhaseProfiles_contDiffOn (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G H J : ComplexComponents) :
    ContDiffOn ℝ ∞ (highGaugePhaseProfiles m w a G H J) wardLowProfileDomain := by
  have hC : ContDiffOn ℝ ∞ (fun x : WardLowPoint =>
      (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ)) wardLowProfileDomain := by
    apply (Complex.ofRealCLM.contDiff.comp_contDiffOn (cyclicLowNormalizedPhase_contDiffOn a ha)).comp
      (contDiff_fst.prodMk ((contDiff_snd.snd.smul contDiff_fst).prodMk contDiff_snd.fst)).contDiffOn
    exact fun _ hx => hx
  have hR : ContDiff ℝ ∞ wardHighThirdVector := (contDiff_snd.fst.add (contDiff_snd.snd.smul contDiff_fst)).neg
  have hDir := endpointDirection_contDiffOn.comp hR.contDiffOn wardHighThirdVector_ne_zero
  have hV (i : Fin 4) : ContDiffOn ℝ ∞
      (fun x : WardLowPoint => normalizedGaugePotential (endpointDirection (wardHighThirdVector x)) G i)
        wardLowProfileDomain := (normalizedGaugePotential_contDiff G i).comp_contDiffOn hDir
  have hRN := Complex.ofRealCLM.contDiff.comp_contDiffOn (hR.contDiffOn.norm ℝ wardHighThirdVector_ne_zero)
  have hInv := hRN.inv (fun x hx => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (wardHighThirdVector_ne_zero x hx)))
  have hC' := (hC.mul (contDiffOn_const (c := (w : ℂ)))).mul (hInv.pow 2)
  exact (hC'.mul (wardHighGaugeBracket_smooth m _ H J _ _ hV contDiff_snd.fst.contDiffOn)).prodMk
    (hC'.mul (wardHighGaugeBracket_smooth m _ J H _ _ hV contDiff_fst.contDiffOn))

/-- Exact `ρ²` and `ρ` powers for the two physical phases in the high-gauge
one-low branch. The gauge covector belongs to the actual third slot. -/
theorem highGaugePhase_eq_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) (hlow : ‖p‖ / ‖q‖ < 1 / 2)
    (G H J : ComplexComponents) :
    let r := -(p + q)
    let x : WardLowPoint := (endpointDirection p, endpointDirection q, ‖p‖ / ‖q‖)
    let v : ComplexCovector := fun i => (‖r‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection r) G i
    let pair := frozenWardScreenPair m H J
    (signedCyclicPhase a p q : ℂ) * (w : ℂ) *
        ((quadratic m p : ℂ) * wardHighGaugeBracket m pair H J v q +
          (quadratic m q : ℂ) * wardHighGaugeBracket m pair J H v p) /
        ((‖p‖ * ‖q‖ * ‖r‖ : ℝ) : ℂ) =
      (highGaugePhaseProfiles m w a G H J x).1 * (x.2.2 : ℂ)^2 * (normalizedFrozenPhase m p : ℂ) +
        (highGaugePhaseProfiles m w a G H J x).2 * (x.2.2 : ℂ) * (normalizedFrozenPhase m q : ℂ) := by
  intro r x v pair
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
  let V := normalizedGaugePotential (endpointDirection (wardHighThirdVector x)) G
  have hv : v = fun i => (‖r‖⁻¹ : ℝ) * V i := by
    funext i
    change (‖r‖⁻¹ : ℝ) * normalizedGaugePotential (endpointDirection r) G i = _
    rw [hrDir]
  have hQBracket := wardHighGaugeBracket_scale m pair H J V x.2.1 ‖r‖⁻¹ ‖q‖
  have hPBracket := wardHighGaugeBracket_scale m pair J H V x.1 ‖r‖⁻¹ ‖p‖
  rw [hQ, ← hv] at hQBracket
  rw [hP, ← hv] at hPBracket
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
  rw [hc, hQBracket, hPBracket, hPhase p hp₀, hPhase q hq₀, hrNorm]
  have Hp : (‖p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp₀.ne'
  have Hq : (‖q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have HR : (‖wardHighThirdVector x‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hR)
  have hRatio : (x.2.2 : ℂ) = (‖p‖ : ℂ) / (‖q‖ : ℂ) := Complex.ofReal_div _ _
  simp only [highGaugePhaseProfiles, hRatio, Complex.ofReal_mul, Complex.ofReal_inv]
  dsimp only [V, pair]
  field_simp

end Burnett.C02
