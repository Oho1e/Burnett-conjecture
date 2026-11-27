import Burnett.Analysis.GaugeProjection.CoefficientCutoff
import Burnett.Analysis.GaugeProjection.SmoothLipschitzApproximation
import Burnett.Analysis.Sobolev.SchwartzHminusDual

set_option autoImplicit false
set_option maxHeartbeats 3500000

noncomputable section

namespace Burnett.A08

open Filter Set Metric Burnett.A02.FrequencySplit
open Burnett.P01
open scoped ContDiff NNReal Topology

open private realPart from Burnett.Analysis.Sobolev.SchwartzHminusDual
open private coefficientBump coefficientBump_one coefficientDilation
  from Burnett.Analysis.GaugeProjection.CoefficientCutoff

/-- The plateau radius for the spatial coefficient cutoff is independent
of its smooth input. This allows the input to vary with the radius. -/
private theorem projectionCoefficientCutoff_uniform_plateau (x : E) :
    ∀ᶠ n : ℕ in atTop, ∀ (g : E → ℂ) (hg : ContDiff ℝ ∞ g),
      projectionCoefficientCutoff g hg n x = g x - g 0 := by
  obtain ⟨N, hN⟩ := exists_nat_ge ‖x‖
  filter_upwards [eventually_ge_atTop N] with n hn g hg
  have hr : ‖x‖ ≤ CMBilinearDual.inputCutoffRadius n := by
    unfold CMBilinearDual.inputCutoffRadius
    exact hN.trans (le_trans (by exact_mod_cast hn) (le_add_of_nonneg_right zero_le_one))
  have hscale := CMBilinearDual.inputCutoffRadius_pos n
  have h : ‖coefficientDilation n x‖ ≤ 1 := by
    change ‖(CMBilinearDual.inputCutoffRadius n)⁻¹ • x‖ ≤ 1
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hscale.le), ← div_eq_inv_mul]
    exact (div_le_one hscale).mpr hr
  change coefficientBump (coefficientDilation n x) * (g x - g 0) = _
  rw [coefficientBump_one h, one_mul]

/-- Real Schwartz coefficients with a fixed Lipschitz cost approximate
any actual globally Lipschitz coefficient modulo its constant at zero. -/
theorem exists_realSchwartz_normalized_Lipschitz_approximation :
    ∃ C : ℝ≥0, 1 ≤ C ∧ ∀ (d : E → ℝ) (L : ℝ≥0), LipschitzWith L d →
      ∃ v : ℕ → SchwartzMap E ℝ,
        (∀ n, v n 0 = 0) ∧
        (∀ n, LipschitzWith (C * L) (v n)) ∧
        ∀ x : E, Tendsto (fun n => v n x) atTop (𝓝 (d x - d 0)) := by
  refine ⟨projectionCoefficientCutoffConstant, le_add_of_nonneg_right (by positivity), ?_⟩
  intro d L hL
  let f (x : E) : ℂ := d x
  have hf : LipschitzWith L f := by
    simpa only [one_mul] using Complex.isometry_ofReal.lipschitz.comp hL
  let ε (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)
  have hε (n : ℕ) : 0 < ε n := by dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  choose g hg hLip hClose using fun n => exists_smooth_lipschitz_approximation f L hf (ε n) (hε n)
  let cut (n : ℕ) := projectionCoefficientCutoff (g n) (hg n) n
  let v (n : ℕ) : SchwartzMap E ℝ := realPart (cut n)
  have hZero (n : ℕ) : v n 0 = 0 := by
    change (coefficientBump (coefficientDilation n 0) * (g n 0 - g n 0)).re = 0
    rw [sub_self, mul_zero, Complex.zero_re]
  have hBound (n : ℕ) : LipschitzWith (projectionCoefficientCutoffConstant * L) (v n) := by
    apply lipschitzWith_iff_norm_sub_le.2
    intro x y
    change ‖(cut n x).re - (cut n y).re‖ ≤ _
    rw [← Complex.sub_re, Real.norm_eq_abs]
    exact (Complex.abs_re_le_norm _).trans
      ((projectionCoefficientCutoff_lipschitz (g n) (hg n) L (hLip n) n).norm_sub_le x y)
  have hgLimit (x : E) : Tendsto (fun n => g n x) atTop (𝓝 (f x)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    refine squeeze_zero (fun _ => norm_nonneg _) (fun n => hClose n x) ?_
    simpa only [mul_zero] using hεlim.const_mul (L : ℝ)
  refine ⟨v, hZero, hBound, fun x => ?_⟩
  have hd := Complex.continuous_re.continuousAt.tendsto.comp ((hgLimit x).sub (hgLimit 0))
  have hConverge : Tendsto (fun n => (g n x - g n 0).re) atTop (𝓝 (d x - d 0)) := by
    simpa only [Function.comp_apply, Complex.sub_re, f, Complex.ofReal_re] using hd
  refine hConverge.congr' ?_
  filter_upwards [projectionCoefficientCutoff_uniform_plateau x] with n hn
  exact congrArg Complex.re (hn (g n) (hg n)).symm

end Burnett.A08
