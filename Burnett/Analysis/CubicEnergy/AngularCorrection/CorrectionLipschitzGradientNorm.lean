import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalAnalyticCorrectionBounds

set_option autoImplicit false
set_option maxHeartbeats 8000000

noncomputable section

namespace Burnett.A08

open Filter MeasureTheory Metric Set ContinuousLinearMap
open Burnett.A06 Burnett.A07 Burnett.A02.FrequencySplit Burnett.Fourier
open scoped ComplexConjugate ContDiff Convolution ENNReal NNReal Topology

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private theorem lipschitzWith_of_ae_fderiv_norm_bound {d : E → ℝ} {L K : ℝ≥0}
    (hd : LipschitzWith L d) (hK : ∀ᵐ x : E, ‖fderiv ℝ d x‖ ≤ K) :
    LipschitzWith K d := by
  have approx (ε : ℝ) (hε : 0 < ε) :
      ∃ g : E → ℝ, LipschitzWith K g ∧ ∀ x, ‖g x - d x‖ ≤ L * ε := by
    let bump : ContDiffBump (0 : E) := ⟨ε / 2, ε, half_pos hε, half_lt_self hε⟩
    let k := bump.normed (volume : Measure E)
    let g := k ⋆[lsmul ℝ ℝ, volume] d
    have hg : ContDiff ℝ ∞ g :=
      bump.hasCompactSupport_normed.contDiff_convolution_left _ bump.contDiff_normed
        hd.continuous.locallyIntegrable
    refine ⟨g, lipschitzWith_of_nnnorm_fderiv_le (hg.differentiable (by simp)) ?_, ?_⟩
    · intro x
      have hdx : DifferentiableAt ℝ g x := hg.differentiable (by simp) x
      apply NNReal.coe_le_coe.mp
      change ‖fderiv ℝ g x‖ ≤ K
      apply ContinuousLinearMap.opNorm_le_bound _ K.coe_nonneg
      intro v
      let ψ (y : E) := k (x - y)
      have hc : Continuous ψ := bump.continuous_normed.comp (continuous_const.sub continuous_id)
      have hcompact : HasCompactSupport ψ :=
        bump.hasCompactSupport_normed.comp_homeomorph (Homeomorph.subLeft x)
      have hψ : Integrable ψ := hc.integrable_of_hasCompactSupport hcompact
      have hnonneg (y : E) : 0 ≤ ψ y := bump.nonneg_normed _
      have hmass : ∫ y, ψ y = 1 :=
        (integral_sub_left_eq_self k volume x).trans bump.integral_normed
      have hmul (a : E) : Integrable (fun y => d (y + a) * ψ y) :=
        ((hd.continuous.comp (continuous_add_right a)).mul hc).integrable_of_hasCompactSupport
          hcompact.mul_left
      have htranslate (a : E) : (∫ y, d (y + a) * ψ y) = g (x + a) := by
        calc
          _ = ∫ y, d ((x-y)+a) * ψ (x-y) :=
            (integral_sub_left_eq_self _ volume x).symm
          _ = _ := by
            change _ = ∫ y, k y • d (x+a-y)
            apply integral_congr_ae
            filter_upwards with y
            have ha : x-y+a = x+a-y := by abel
            change d (x-y+a) * k (x-(x-y)) = k y • d (x+a-y)
            rw [ha, sub_sub_cancel, smul_eq_mul, mul_comm]
      have hmul₀ : Integrable (fun y => d y * ψ y) := by simpa using hmul 0
      have htranslate₀ : (∫ y, d y * ψ y) = g x := by simpa using htranslate 0
      have hslope (t : ℝ) :
          (∫ y, (t⁻¹ • (d (y+t • v)-d y)) * ψ y) =
            t⁻¹ • (g (x+t • v)-g x) := by
        simp_rw [smul_eq_mul, mul_assoc, sub_mul]
        rw [integral_const_mul, integral_sub (hmul (t • v)) hmul₀, htranslate, htranslate₀]
      have hlim := hd.integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul hψ v
      have hef : (fderiv ℝ g x) v = ∫ y, lineDeriv ℝ d y v * ψ y :=
        tendsto_nhds_unique (hdx.hasFDerivAt.hasLineDerivAt v).tendsto_slope_zero_right
          (hlim.congr hslope)
      have hrad : ∀ᵐ y : E, DifferentiableAt ℝ d y := hd.ae_differentiableAt
      have hpoint : ∀ᵐ y : E, ‖lineDeriv ℝ d y v * ψ y‖ ≤ ((K : ℝ) * ‖v‖) * ψ y := by
        filter_upwards [hrad,hK] with y hDy hsup
        rw [norm_mul, hDy.lineDeriv_eq_fderiv, Real.norm_of_nonneg (hnonneg y)]
        exact mul_le_mul_of_nonneg_right
          (((fderiv ℝ d y).le_opNorm v).trans (mul_le_mul_of_nonneg_right hsup (norm_nonneg _)))
          (hnonneg y)
      have hbound := hψ.const_mul ((K : ℝ) * ‖v‖)
      have hprod : Integrable (fun y => lineDeriv ℝ d y v * ψ y) :=
        hbound.mono' ((aestronglyMeasurable_lineDeriv hd.continuous volume).mul hψ.aestronglyMeasurable)
          hpoint
      rw [hef]
      calc
        _ ≤ ∫ y, ‖lineDeriv ℝ d y v * ψ y‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ y, ((K : ℝ) * ‖v‖) * ψ y := integral_mono_ae hprod.norm hbound hpoint
        _ = _ := by rw [integral_const_mul, hmass, mul_one]
    · intro x
      rw [← dist_eq_norm]
      refine bump.dist_normed_convolution_le hd.continuous.aestronglyMeasurable (fun y hy => ?_)
      exact (hd.dist_le_mul y x).trans (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le L.coe_nonneg)
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose g hg hnear using fun n => approx (ε n) (hε n)
  have hconv (x : E) : Tendsto (fun n => g n x) atTop (𝓝 (d x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun n => hnear n x)
      (by simpa only [mul_zero] using hεlim.const_mul (L : ℝ))
  apply lipschitzWith_iff_norm_sub_le.2
  intro x y
  exact le_of_tendsto' ((hconv x).sub (hconv y)).norm (fun n => (hg n).norm_sub_le x y)

/-- The essential-supremum gradient norm of a real Lipschitz scalar on
Euclidean space. The Fréchet derivative is the scalar gradient covector. -/
def lipschitzGradientLInfty (d : E → ℝ) : ℝ :=
  (eLpNorm (fderiv ℝ d) ⊤ (volume : Measure E)).toReal

/-- A real Lipschitz function on Euclidean space is Lipschitz with the
essential supremum of its almost-everywhere gradient norm. -/
theorem lipschitzWith_lipschitzGradientLInfty {d : E → ℝ} {L : ℝ≥0}
    (hd : LipschitzWith L d) : LipschitzWith (lipschitzGradientLInfty d).toNNReal d := by
  let A : ℝ≥0∞ := eLpNormEssSup (fderiv ℝ d) (volume : Measure E)
  have hA : A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (eLpNormEssSup_le_of_ae_bound (.of_forall (fun _ : E => norm_fderiv_le_of_lipschitz ℝ hd)))
  have hK : ∀ᵐ x : E, ‖fderiv ℝ d x‖ ≤ (lipschitzGradientLInfty d).toNNReal := by
    have hs := ENNReal.ae_le_essSup (μ := (volume : Measure E)) (fun x => ‖fderiv ℝ d x‖ₑ)
    filter_upwards [hs] with x hx
    change ‖fderiv ℝ d x‖ₑ ≤ A at hx
    rw [← ENNReal.coe_toNNReal hA, enorm_le_coe] at hx
    simpa only [lipschitzGradientLInfty, eLpNorm_exponent_top, ENNReal.toNNReal_toReal_eq, A] using
      (show ‖fderiv ℝ d x‖ ≤ (A.toNNReal : ℝ) from hx)
  exact lipschitzWith_of_ae_fderiv_norm_bound hd hK

/-- The rough estimate with the original essential-supremum gradient norm
of the coefficient. Rademacher's theorem supplies its a.e. interpretation. -/
theorem OriginalAnalyticCorrectionBounds.lipschitz_commutator_gradientLInfty
    {b : Joint → ℂ} {C : ℝ} (P : OriginalAnalyticCorrectionBounds b C)
    (d : E → ℝ) {L : ℝ≥0} (hd : LipschitzWith L d) (H v : SchwartzMap E ℂ) :
    ∃ U V : FirstOrderLp 2,
      ‖U‖ ≤ C * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖ * ‖v.toLp 4 volume‖ ∧
      ‖V‖ ≤ C * lipschitzGradientLInfty d * ‖H.toLp 4 volume‖ * ‖v.toLp 4 volume‖ ∧
      ∀ w : SchwartzMap E ℂ,
        inner ℂ (w.toLp 2 volume) U = -radianHighCommutatorPair b d H v w ∧
        inner ℂ (w.toLp 2 volume) V =
          -radianHighCommutatorPair (highAdjointSymbol b) d (fun x => conj (H x)) v w := by
  have h0 : 0 ≤ lipschitzGradientLInfty d := ENNReal.toReal_nonneg
  simpa only [Real.coe_toNNReal _ h0] using
    P.lipschitz_commutator d _ (lipschitzWith_lipschitzGradientLInfty hd) H v

end Burnett.A08
