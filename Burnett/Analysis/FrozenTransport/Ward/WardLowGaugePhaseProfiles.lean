import Burnett.Analysis.FrozenTransport.Ward.ActualWardPhaseSchwartz
import Burnett.Analysis.FrozenTransport.GaugeCorrection.CyclicLowPhaseSmooth
import Burnett.Analysis.FrozenTransport.GaugeCorrection.NormalizedGaugePotentialJets
import Burnett.Analysis.FrozenTransport.GaugeCorrection.OriginalLowGaugeCorrection

set_option autoImplicit false
set_option maxRecDepth 5800
set_option maxHeartbeats 11500000
noncomputable section

namespace Burnett.C02

open Set Matrix Burnett.RicciSymbol Burnett.V08 Burnett.P01
open Burnett.A02.FrequencySplit (E)
open Burnett.Analysis.ProjectiveNullCaps (quadratic)
open scoped BigOperators ContDiff Matrix

abbrev WardLowPoint := E × E × ℝ

/-- The precise bilinear frozen screen contraction in paper line 2102. -/
def frozenWardScreenPair (m : Tensor2) (H J : ComplexComponents) : ℂ :=
  (1 / 4 : ℂ) * ∑ a : Fin 4, ∑ b : Fin 4, ∑ i : Fin 4, ∑ j : Fin 4,
    (m a i : ℂ) * (m b j : ℂ) * H i j * J a b

/-- The raised gauge generator contracted with a real covector. -/
def raisedWardGaugeDot (m : Tensor2) (v : Burnett.P01.ComplexCovector) (p : E) : ℂ :=
  ∑ i : Fin 4, ∑ j : Fin 4, (m i j : ℂ) * v j * (p i : ℂ)

private theorem raisedWardGaugeDot_scale (m : Tensor2) (v : Burnett.P01.ComplexCovector) (dir : E)
    (s : ℝ) (hs : s ≠ 0) :
    raisedWardGaugeDot m (fun j => ((s⁻¹ : ℝ) : ℂ) * v j) (s • dir) = raisedWardGaugeDot m v dir := by
  unfold raisedWardGaugeDot
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [PiLp.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_inv]
  have h : (s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  field_simp

private theorem raisedWardGaugeDot_normalized_contDiff (m : Tensor2) (G : ComplexComponents) :
    ContDiff ℝ ∞ (fun dir : E => raisedWardGaugeDot m (normalizedGaugePotential dir G) dir) := by
  unfold raisedWardGaugeDot
  exact ContDiff.sum fun i _ => ContDiff.sum fun j _ =>
    (contDiff_const.mul (normalizedGaugePotential_contDiff G j)).mul
      (Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff)

def wardLowProfileDomain : Set WardLowPoint :=
  {x | (1 / 4 : ℝ) < ‖x.1‖ ∧ ‖x.2.2 • x.1‖ < 1 / 2 ∧ 3 / 4 < ‖x.2.1‖}

theorem wardLowProfileDomain_open : IsOpen wardLowProfileDomain := by
  exact (isOpen_lt continuous_const continuous_fst.norm).inter
    ((isOpen_lt (continuous_snd.snd.smul continuous_fst).norm continuous_const).inter
      (isOpen_lt continuous_const continuous_snd.fst.norm))

/-- The middle term of line 2143 with the physical phase moved to its
own slot. The first profile leaves that phase on the second slot and
the second profile leaves it on the third slot. -/
def lowGaugeScalarPhaseProfiles (m : Tensor2) (w : ℝ) (a : E → ℝ) (G H J : ComplexComponents)
    (x : WardLowPoint) : ℂ × ℂ :=
  let A := (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ) * (w : ℂ) *
    raisedWardGaugeDot m (normalizedGaugePotential x.1 G) x.1 * frozenWardScreenPair m H J
  let s := (‖x.2.1 + x.2.2 • x.1‖ : ℂ)
  (A / s, A * s)

theorem lowGaugeScalarPhaseProfiles_contDiffOn (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (G H J : ComplexComponents) :
    ContDiffOn ℝ ∞ (lowGaugeScalarPhaseProfiles m w a G H J) wardLowProfileDomain := by
  have hC : ContDiffOn ℝ ∞ (fun x : WardLowPoint =>
      (cyclicLowNormalizedPhase a x.1 (x.2.2 • x.1) x.2.1 : ℂ)) wardLowProfileDomain := by
    apply (Complex.ofRealCLM.contDiff.comp_contDiffOn (cyclicLowNormalizedPhase_contDiffOn a ha)).comp
      (contDiff_fst.prodMk ((contDiff_snd.snd.smul contDiff_fst).prodMk contDiff_snd.fst)).contDiffOn
    intro x hx
    exact hx
  have hN (x : WardLowPoint) (hx : x ∈ wardLowProfileDomain) : x.2.1 + x.2.2 • x.1 ≠ 0 := by
    intro hZero
    have hEq : x.2.1 = -(x.2.2 • x.1) := eq_neg_of_add_eq_zero_left hZero
    have h := hx.2.2
    rw [hEq, norm_neg] at h
    linarith only [h, hx.2.1]
  have hS : ContDiffOn ℝ ∞ (fun x : WardLowPoint => (‖x.2.1 + x.2.2 • x.1‖ : ℂ)) wardLowProfileDomain :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (((contDiff_snd.fst.add (contDiff_snd.snd.smul contDiff_fst)).contDiffOn).norm ℝ hN)
  have hA := (((hC.mul (contDiffOn_const (c := (w : ℂ)))).mul
    ((raisedWardGaugeDot_normalized_contDiff m G).comp contDiff_fst).contDiffOn).mul
      (contDiffOn_const (c := frozenWardScreenPair m H J)))
  unfold lowGaugeScalarPhaseProfiles
  simpa only [div_eq_mul_inv] using
    (hA.mul (hS.inv fun x hx => Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hN x hx)))).prodMk
      (hA.mul hS)

/-- Exact normalization of both phase factors in the first of the
three phase-bearing low gauge summands. The ratio is kept at zero
by the same cyclic extension and the two high magnitudes stay in
their actual slots. -/
theorem lowGaugeScalarPhase_eq_normalized (m : Tensor2) (w : ℝ) (a : E → ℝ)
    (ha : ContDiffOn ℝ ∞ a {ξ : E | ξ ≠ 0}) (hOdd : ∀ ξ, a (-ξ) = -a ξ)
    (hHom : ∀ t : ℝ, 0 < t → ∀ ξ, a (t • ξ) = t * a ξ)
    (p q : E) (hp : p ≠ 0) (hq : q ≠ 0) (hlow : ‖p‖ / ‖q‖ < 1 / 2)
    (G H J : ComplexComponents) :
    let r := -(p + q)
    let dir := ‖p‖⁻¹ • p
    let θ := ‖q‖⁻¹ • q
    let ρ := ‖p‖ / ‖q‖
    let v (i : Fin 4) := ((‖p‖⁻¹ : ℝ) : ℂ) * normalizedGaugePotential dir G i
    (signedCyclicPhase a p q : ℂ) * (w : ℂ) * raisedWardGaugeDot m v p *
        ((quadratic m q : ℂ) + (quadratic m r : ℂ)) * frozenWardScreenPair m H J /
        ((‖p‖ * ‖q‖ * ‖r‖ : ℝ) : ℂ) =
      (lowGaugeScalarPhaseProfiles m w a G H J (dir,θ,ρ)).1 * (normalizedFrozenPhase m q : ℂ) +
        (lowGaugeScalarPhaseProfiles m w a G H J (dir,θ,ρ)).2 * (normalizedFrozenPhase m r : ℂ) := by
  intro r dir θ ρ v
  have hp₀ := norm_pos_iff.mpr hp
  have hq₀ := norm_pos_iff.mpr hq
  have hpEq : ‖p‖ • dir = p := smul_inv_smul₀ hp₀.ne' p
  have hqEq : ‖q‖ • θ = q := smul_inv_smul₀ hq₀.ne' q
  have hDir : ‖dir‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hp
  have hθ : ‖θ‖ = 1 := norm_smul_inv_norm (𝕜 := ℝ) hq
  have hρ₀ : 0 ≤ ρ := div_nonneg (norm_nonneg _) (norm_nonneg _)
  have hZ : ‖ρ • dir‖ < 1 / 2 := by rw [norm_smul, Real.norm_of_nonneg hρ₀, hDir, mul_one]; exact hlow
  have hS₀ : 0 < ‖θ + ρ • dir‖ := by
    apply norm_pos_iff.mpr
    intro h
    have hEq : θ = -(ρ • dir) := eq_neg_of_add_eq_zero_left h
    rw [hEq, norm_neg] at hθ
    linarith only [hθ, hZ]
  have hScale : ‖q‖ * ρ = ‖p‖ := by
    change ‖q‖ * (‖p‖ / ‖q‖) = _
    rw [mul_comm, div_mul_cancel₀ _ hq₀.ne']
  have hr : r = -(‖q‖ • (θ + ρ • dir)) := by
    unfold r
    rw [smul_add, hqEq, smul_smul, hScale, hpEq, add_comm p q]
  have hrNorm : ‖r‖ = ‖q‖ * ‖θ + ρ • dir‖ := by
    conv_lhs => rw [hr, norm_neg, norm_smul, Real.norm_of_nonneg hq₀.le]
  have hCyclic := signedCyclicPhase_div_eq_lowNormalized a ha hOdd hHom dir (ρ • dir) θ
    ‖p‖ ‖q‖ hp₀ hq₀ hθ hZ rfl
  rw [hpEq, hqEq] at hCyclic
  have hA : (signedCyclicPhase a p q : ℂ) =
      (cyclicLowNormalizedPhase a dir (ρ • dir) θ : ℂ) * (‖p‖ : ℂ) := by
    exact_mod_cast (div_eq_iff hp₀.ne').mp hCyclic
  have hGauge : raisedWardGaugeDot m v p =
      raisedWardGaugeDot m (normalizedGaugePotential dir G) dir := by
    simpa only [v, hpEq] using
      raisedWardGaugeDot_scale m (normalizedGaugePotential dir G) dir ‖p‖ hp₀.ne'
  have hr₀ : 0 < ‖r‖ := hrNorm.symm ▸ mul_pos hq₀ hS₀
  have hPhase (k : E) (hk : 0 < ‖k‖) :
      (quadratic m k : ℂ) = (normalizedFrozenPhase m k : ℂ) * (‖k‖ : ℂ)^2 := by
    have hReal : quadratic m k = normalizedFrozenPhase m k * ‖k‖^2 :=
      (div_eq_iff (pow_ne_zero 2 hk.ne')).mp (show
        quadratic m k / ‖k‖^2 = normalizedFrozenPhase m k from rfl)
    exact_mod_cast hReal
  have hpC : (‖p‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hp₀.ne'
  have hqC : (‖q‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hq₀.ne'
  have hSC : (‖θ + ρ • dir‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS₀.ne'
  rw [hA, hGauge, hPhase q hq₀, hPhase r hr₀, hrNorm]
  simp only [lowGaugeScalarPhaseProfiles, Complex.ofReal_mul]
  field_simp

end Burnett.C02
