import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderSymbol
import Burnett.Analysis.PrincipalEnergy.Quantization.FiniteFirstOrderAction

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped FourierTransform Topology

def firstOrderHighSymbol (a : E → E → ℂ) (x ξ : E) : ℂ :=
  ((1 - radialCore ξ : ℝ) : ℂ) * a x ξ

def firstOrderHighAction (a : E → E → ℂ) (f : E → ℂ) (x : E) : ℂ :=
  𝓕⁻ (fun ξ => firstOrderHighSymbol a x ξ * (𝓕 f) ξ) x

theorem firstOrderFiniteSymbol_eventually (a : E → E → ℂ) (x ξ : E) :
    (fun N => firstOrderFiniteSymbol a x N ξ) =ᶠ[atTop] (fun _ => firstOrderHighSymbol a x ξ) := by
  have hLarge : ∀ᶠ N : ℕ in atTop, ‖ξ‖ ≤ (2 : ℝ) ^ N :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).eventually (eventually_ge_atTop ‖ξ‖)
  filter_upwards [hLarge] with N hN
  have hs : 0 < dyadicScale N := by unfold dyadicScale; positivity
  have hn : ‖(dyadicScale N)⁻¹ • ξ‖ ≤ 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), ← div_eq_inv_mul]
    exact (div_le_one hs).mpr hN
  rw [firstOrderFiniteSymbol_telescope, radialCore_eq_one _ hn]
  rfl

theorem firstOrderFiniteSymbol_norm_le (a : E → E → ℂ) (x ξ : E) (N : ℕ) :
    ‖firstOrderFiniteSymbol a x N ξ‖ ≤ ‖a x ξ‖ := by
  rw [firstOrderFiniteSymbol_telescope, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  refine mul_le_of_le_one_left (norm_nonneg _) (abs_le.mpr ⟨?_, ?_⟩)
  · linarith [radialCore_nonneg ((dyadicScale N)⁻¹ • ξ), radialCore_le_one ξ]
  · linarith [radialCore_le_one ((dyadicScale N)⁻¹ • ξ), radialCore_nonneg ξ]

/-- The exact frequency cutoffs converge to the infrared-regularized action
on actual scalar Schwartz tests. The dominating Fourier moment uses only
the first growth power in frequency. -/
theorem firstOrderFiniteAction_tendsto (a : E → E → ℂ) (ha : FrequencyOrderOne a)
    (f : SchwartzMap E ℂ) (x : E) :
    Tendsto (fun N => firstOrderFiniteAction a N f x) atTop (𝓝 (firstOrderHighAction a f x)) := by
  obtain ⟨M,hM,hA⟩ := ha.order 0
  have hOrder (ξ : E) : ‖a x ξ‖ ≤ M * (1 + ‖ξ‖) := by
    simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hA x ξ
  let F := SchwartzMap.fourierTransformCLM ℂ f
  change Tendsto (fun N => (𝓕⁻ (fun ξ => firstOrderFiniteSymbol a x N ξ * F ξ)) x) atTop
    (𝓝 ((𝓕⁻ (fun ξ => firstOrderHighSymbol a x ξ * F ξ)) x))
  simp only [Real.fourierIntegralInv_eq]
  have hCut (N : ℕ) : Continuous (firstOrderFiniteSymbol a x N) := by
    rw [show firstOrderFiniteSymbol a x N = fun ξ =>
      ((radialCore ((dyadicScale N)⁻¹ • ξ) - radialCore ξ : ℝ) : ℂ) * a x ξ from
      funext fun ξ => firstOrderFiniteSymbol_telescope a x N ξ]
    exact (Complex.continuous_ofReal.comp ((radialCore_contDiff.continuous.comp
      (continuous_const.smul continuous_id)).sub radialCore_contDiff.continuous)).mul (ha.smooth x).continuous
  have hChar : Continuous (fun ξ : E => Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  let g (ξ : E) := M * ((1 + ‖ξ‖) * ‖F ξ‖)
  refine tendsto_integral_of_dominated_convergence g
    (fun N => (hChar.smul ((hCut N).mul F.continuous)).aestronglyMeasurable) ?_ ?_ ?_
  · have hI := F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)
    simpa only [g, add_mul, one_mul, pow_one] using hI.const_mul M
  · intro N
    filter_upwards with ξ
    rw [Circle.norm_smul, norm_mul]
    calc
      _ ≤ ‖a x ξ‖ * ‖F ξ‖ := mul_le_mul_of_nonneg_right (firstOrderFiniteSymbol_norm_le a x ξ N) (norm_nonneg _)
      _ ≤ g ξ := by
        change _ ≤ M * ((1 + ‖ξ‖) * ‖F ξ‖)
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right (hOrder ξ) (norm_nonneg _)
  · filter_upwards with ξ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [firstOrderFiniteSymbol_eventually a x ξ] with N hN
    rw [hN]

end Burnett.Analysis.FirstOrderDyadic
