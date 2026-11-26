import Burnett.Analysis.CubicEnergy.AngularCorrection.UpperFrequencyCutoffCanonical
import Burnett.Analysis.CubicEnergy.AngularCorrection.OriginalHermitianWeakEnergy

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Burnett.A08

open Burnett.A02.FrequencySplit Burnett.A07 Burnett.Fourier MeasureTheory Filter Metric
open scoped BigOperators ComplexConjugate ENNReal FourierTransform Topology

open private radialBallBump radialLowCutoff radialLowCutoff_eq_one from Burnett.Analysis.CubicEnergy.AngularCorrection.UpperFrequencyCutoffCanonical
open private inner_eq_of_schwartz from Burnett.Analysis.CubicEnergy.AngularCorrection.FirstOrderPairL2Extension

local instance : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
local instance : Fact (1 ≤ (4 : ℝ≥0∞)) := ⟨by norm_num⟩

private abbrev Test := SchwartzMap E ℂ

private def upperFrequencySymbol (Λ : ℝ) : BoundedSymbol E where
  toFun ξ := radialLowCutoff Λ (tau • ξ)
  measurable := (Complex.continuous_ofReal.comp
    (radialBallBump.continuous.comp (continuous_const.smul (continuous_const.smul continuous_id)))).aestronglyMeasurable
  bound := 1
  bound_nonneg := zero_le_one
  norm_le ξ := by
    rw [Complex.norm_real]
    change ‖radialBallBump (Λ⁻¹ • (tau • ξ))‖ ≤ 1
    rw [Real.norm_of_nonneg radialBallBump.nonneg]
    exact radialBallBump.le_one

/-- The original upper cutoff on the actual L² output of the correction. -/
def upperFrequencyCutoffL2 (Λ : ℝ) : FirstOrderLp 2 →L[ℂ] FirstOrderLp 2 :=
  fourierMultiplier (upperFrequencySymbol Λ)

theorem upperFrequencyCutoffL2_norm_le (Λ : ℝ) (x : FirstOrderLp 2) :
    ‖upperFrequencyCutoffL2 Λ x‖ ≤ ‖x‖ := by
  simpa only [upperFrequencyCutoffL2, upperFrequencySymbol, one_mul] using
    fourierMultiplier_norm_le (upperFrequencySymbol Λ) x

theorem upperFrequencyCutoffL2_toLp (Λ : ℝ) (v : Test) :
    upperFrequencyCutoffL2 Λ (v.toLp 2 volume) = (upperFrequencyCutoff Λ v).toLp 2 volume := by
  apply fourierL2Equiv.injective
  rw [upperFrequencyCutoffL2, fourier_fourierMultiplier]
  apply Lp.ext
  filter_upwards [symbolL2_ae (upperFrequencySymbol Λ) (fourierL2Equiv (v.toLp 2 volume)),
    fourierL2Equiv_schwartz_ae v, fourierL2Equiv_schwartz_ae (upperFrequencyCutoff Λ v)] with ξ hs hv hj
  rw [hs, hv, hj, upperFrequencyCutoff_fourier, mul_comm]
  rfl

theorem upperFrequencyCutoffL2_symmetric (Λ : ℝ) (x y : FirstOrderLp 2) :
    inner ℂ x (upperFrequencyCutoffL2 Λ y) = inner ℂ (upperFrequencyCutoffL2 Λ x) y := by
  let F := fourierL2Equiv (V := E)
  rw [← F.inner_map_map x (upperFrequencyCutoffL2 Λ y),
    ← F.inner_map_map (upperFrequencyCutoffL2 Λ x) y]
  change inner ℂ (F x) (fourierL2Equiv (fourierMultiplier (upperFrequencySymbol Λ) y)) =
    inner ℂ (fourierL2Equiv (fourierMultiplier (upperFrequencySymbol Λ) x)) (F y)
  rw [fourier_fourierMultiplier, fourier_fourierMultiplier, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [symbolL2_ae (upperFrequencySymbol Λ) (F x),
    symbolL2_ae (upperFrequencySymbol Λ) (F y)] with ξ hx hy
  rw [hx, hy, RCLike.inner_apply', RCLike.inner_apply', map_mul]
  change conj (F x ξ) * ((radialLowCutoff Λ (tau • ξ) : ℂ) * F y ξ) =
    conj (radialLowCutoff Λ (tau • ξ) : ℂ) * conj (F x ξ) * F y ξ
  rw [Complex.conj_ofReal]
  ring

private theorem norm_upperFrequencySymbol_sub_one (Λ : ℝ) (ξ : E) :
    ‖upperFrequencySymbol Λ ξ - 1‖ ≤ 1 := by
  have h₀ : 0 ≤ radialLowCutoff Λ (tau • ξ) := radialBallBump.nonneg
  have h₁ : radialLowCutoff Λ (tau • ξ) ≤ 1 := radialBallBump.le_one
  change ‖(radialLowCutoff Λ (tau • ξ) : ℂ) - 1‖ ≤ 1
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith only [h₀], by linarith only [h₁]⟩

/-- Strong convergence of the same cutoff on L², applied to the actual
output without any regularity requirement on its spatial representative. -/
theorem upperFrequencyCutoffL2_tendsto (x : FirstOrderLp 2) :
    Tendsto (fun Λ : ℝ => upperFrequencyCutoffL2 Λ x) atTop (𝓝 x) := by
  let y := fourierL2Equiv x
  let error (Λ : ℝ) (ξ : E) := ‖(upperFrequencySymbol Λ ξ - 1) * y ξ‖^2
  have eq (Λ : ℝ) : ‖upperFrequencyCutoffL2 Λ x - x‖^2 = ∫ ξ, error Λ ξ := by
    rw [← fourierL2Equiv.norm_map (upperFrequencyCutoffL2 Λ x - x), map_sub,
      upperFrequencyCutoffL2, fourier_fourierMultiplier, l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (symbolL2 (upperFrequencySymbol Λ) y) y,
      symbolL2_ae (upperFrequencySymbol Λ) y] with ξ hf hs
    change ‖(symbolL2 (upperFrequencySymbol Λ) y - y) ξ‖^2 = error Λ ξ
    rw [hf, Pi.sub_apply, hs]
    simp only [error, sub_mul, one_mul]
  have hMeas (Λ : ℝ) : AEStronglyMeasurable (error Λ) (volume : Measure E) :=
    (((upperFrequencySymbol Λ).measurable.sub aestronglyMeasurable_const).mul (Lp.aestronglyMeasurable y)).norm.pow 2
  have hInt : Integrable (fun ξ : E => ‖y ξ‖^2) :=
    (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable y)).mp (Lp.memLp y)
  have hBound (Λ : ℝ) (ξ : E) : ‖error Λ ξ‖ ≤ ‖y ξ‖^2 := by
    change ‖‖(upperFrequencySymbol Λ ξ - 1) * y ξ‖^2‖ ≤ ‖y ξ‖^2
    rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul]
    exact pow_le_pow_left₀ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (mul_le_of_le_one_left (norm_nonneg _) (norm_upperFrequencySymbol_sub_one Λ ξ)) _
  have point (ξ : E) : Tendsto (fun Λ : ℝ => error Λ ξ) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop (max (1 : ℝ) ‖tau • ξ‖)] with Λ hΛ
    have hp : 0 < Λ := lt_of_lt_of_le zero_lt_one ((le_max_left _ _).trans hΛ)
    have h1 := radialLowCutoff_eq_one hp ((le_max_right _ _).trans hΛ)
    simp [error, upperFrequencySymbol, h1]
  have integralLimit := tendsto_integral_filter_of_dominated_convergence
    (F := error) (f := fun _ : E => (0 : ℝ)) (l := atTop)
    (fun ξ => ‖y ξ‖^2) (Eventually.of_forall hMeas)
    (Eventually.of_forall fun Λ => Eventually.of_forall (hBound Λ)) hInt (Eventually.of_forall point)
  have sqLimit : Tendsto (fun Λ : ℝ => ‖upperFrequencyCutoffL2 Λ x - x‖^2) atTop (𝓝 0) := by
    simpa only [eq, integral_zero] using integralLimit
  exact tendsto_iff_norm_sub_tendsto_zero.mpr
    (by simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using sqLimit.sqrt)

/-- The actual same cutoff on the input and the L² output. -/
def symmetricUpperCutoffOutput (R : Test → FirstOrderLp 2) (Λ : ℝ) (u : Test) : FirstOrderLp 2 :=
  upperFrequencyCutoffL2 Λ (R (upperFrequencyCutoff Λ u))

theorem inner_symmetricUpperCutoffOutput (R : Test → FirstOrderLp 2) (Λ : ℝ) (u w : Test) :
    inner ℂ (w.toLp 2 volume) (symmetricUpperCutoffOutput R Λ u) =
      inner ℂ ((upperFrequencyCutoff Λ w).toLp 2 volume) (R (upperFrequencyCutoff Λ u)) := by
  rw [symmetricUpperCutoffOutput, upperFrequencyCutoffL2_symmetric, upperFrequencyCutoffL2_toLp]

theorem symmetricUpperCutoffOutput_symmetric (R : Test → FirstOrderLp 2)
    (symmetric : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (R u) = inner ℂ (R w) (u.toLp 2 volume))
    (Λ : ℝ) (u w : Test) :
    inner ℂ (w.toLp 2 volume) (symmetricUpperCutoffOutput R Λ u) =
      inner ℂ (symmetricUpperCutoffOutput R Λ w) (u.toLp 2 volume) := by
  rw [inner_symmetricUpperCutoffOutput, symmetric, symmetricUpperCutoffOutput,
    ← upperFrequencyCutoffL2_toLp, upperFrequencyCutoffL2_symmetric]

/-- Strong removal at fixed Schwartz input and fixed Hermitian correction
uses only the original four high coordinate L⁴ derivatives. -/
theorem symmetricUpperCutoffOutput_tendsto (R : Test → FirstOrderLp 2) (C : ℝ)
    (symmetric : ∀ u w : Test, inner ℂ (w.toLp 2 volume) (R u) = inner ℂ (R w) (u.toLp 2 volume))
    (bound : ∀ u : Test, ‖R u‖ ≤ C * highDerivativeLp4Sum u) (u : Test) :
    Tendsto (fun Λ : ℝ => symmetricUpperCutoffOutput R Λ u) atTop (𝓝 (R u)) := by
  have sub (v w : Test) : R (v - w) = R v - R w := by
    apply inner_eq_of_schwartz
    intro z
    rw [inner_sub_right, symmetric (v - w) z, symmetric v z, symmetric w z]
    change inner ℂ (R z) ((SchwartzMap.toLpCLM ℂ ℂ 2 volume) (v - w)) =
      inner ℂ (R z) (v.toLp 2 volume) - inner ℂ (R z) (w.toLp 2 volume)
    rw [map_sub, inner_sub_right]
    rfl
  have split (Λ : ℝ) : symmetricUpperCutoffOutput R Λ u - R u =
      upperFrequencyCutoffL2 Λ (R (upperFrequencyError Λ u)) +
        (upperFrequencyCutoffL2 Λ (R u) - R u) := by
    rw [symmetricUpperCutoffOutput, upperFrequencyError, sub, map_sub]
    abel
  have smallInput : Tendsto (fun Λ : ℝ => highDerivativeLp4Sum (upperFrequencyError Λ u)) atTop (𝓝 0) := by
    simpa only [highDerivativeLp4Sum, Finset.sum_const_zero] using (tendsto_finset_sum Finset.univ fun j _ =>
      (coordinateDerivative_upperFrequencyError_tendsto_L2_L4 j u).2)
  have smallOutput : Tendsto (fun Λ : ℝ => ‖upperFrequencyCutoffL2 Λ (R u) - R u‖) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (upperFrequencyCutoffL2_tendsto (R u))
  have majorant : Tendsto (fun Λ : ℝ => C * highDerivativeLp4Sum (upperFrequencyError Λ u) +
      ‖upperFrequencyCutoffL2 Λ (R u) - R u‖) atTop (𝓝 0) := by
    simpa only [mul_zero, zero_add] using (smallInput.const_mul C).add smallOutput
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  refine squeeze_zero (fun _ => norm_nonneg _) (fun Λ => ?_) majorant
  rw [split]
  exact (norm_add_le _ _).trans (add_le_add_right
    ((upperFrequencyCutoffL2_norm_le Λ _).trans (bound _)) _)

end Burnett.A08
