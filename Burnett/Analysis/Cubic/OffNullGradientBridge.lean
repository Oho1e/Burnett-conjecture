import Burnett.Analysis.Cubic.OffNullCutoff

noncomputable section

namespace Burnett.CubicOffNull

open MeasureTheory Filter CubicExplicit
open X02.SobolevTestJet
open scoped Topology ContDiff

def cutoffProduct (χ : Cutoff) (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) : Cutoff :=
  ⟨fun x => (χ : Space → ℝ) x * h x,
    (test_smooth χ).mul hh, (test_compactSupport χ).mul_right⟩

def localizedGradient (χ : Cutoff) (h : Space → ℝ) (i : Index) (x : Space) : ℝ :=
  (χ : Space → ℝ) x * CubicExplicit.D i h x

theorem localizedGradient_memLp (χ : Cutoff) {h : Space → ℝ}
    (hh : ContDiff ℝ ∞ h) (i : Index) :
    MemLp (localizedGradient χ h i) 2 (volume : Measure Space) := by
  have hc : Continuous (CubicExplicit.D i h) :=
    ((hh.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const))
  exact ((test_smooth χ).continuous.mul hc).memLp_of_hasCompactSupport
    ((test_compactSupport χ).mul_right)

def localizedGradientLp (χ : Cutoff) (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (i : Index) : ScalarL2 :=
  (localizedGradient_memLp χ hh i).toLp (localizedGradient χ h i)

def productGradientLp (χ : Cutoff) (h : Space → ℝ) (hh : ContDiff ℝ ∞ h) (i : Index) : ScalarL2 :=
  directionalLp i (cutoffProduct χ h hh)

theorem productGradientLp_sub_localizedGradientLp (χ : Cutoff) (h : Space → ℝ)
    (hh : ContDiff ℝ ∞ h) (i : Index) :
    productGradientLp χ h hh i - localizedGradientLp χ h hh i =
      (cutoffError_memLp χ hh.continuous i).toLp (cutoffError χ h i) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (productGradientLp χ h hh i) (localizedGradientLp χ h hh i),
    (directional_memLp i (cutoffProduct χ h hh)).coeFn_toLp,
    (localizedGradient_memLp χ hh i).coeFn_toLp,
    (cutoffError_memLp χ hh.continuous i).coeFn_toLp] with x hsub hp hl he
  rw [hsub]
  change ((productGradientLp χ h hh i : Space → ℝ) x -
    (localizedGradientLp χ h hh i : Space → ℝ) x) = _
  change (productGradientLp χ h hh i : Space → ℝ) x = _ at hp
  change (localizedGradientLp χ h hh i : Space → ℝ) x = _ at hl
  rw [hp, hl, he]
  exact cutoff_gradient_identity χ (hh.differentiable (by simp)) i x

/-- The two cutoff placements differ by a strongly vanishing L² sequence
after every fixed actual continuous linear map. -/
theorem f_productGradient_map_difference_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ScalarL2 →L[ℝ] E) (χ : Cutoff) (i : Index) :
    Tendsto (fun n => A (productGradientLp χ (fSequence n) (fSequence_smooth n) i) -
      A (localizedGradientLp χ (fSequence n) (fSequence_smooth n) i)) atTop (𝓝 0) := by
  simpa only [← map_sub, productGradientLp_sub_localizedGradientLp, fCutoffErrorLp] using
    map_fCutoffErrorLp_tendsto_zero A χ i

theorem w_productGradient_map_difference_tendsto_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (A : ScalarL2 →L[ℝ] E) (χ : Cutoff) (i : Index) :
    Tendsto (fun n => A (productGradientLp χ (wSequence n) (wSequence_smooth n) i) -
      A (localizedGradientLp χ (wSequence n) (wSequence_smooth n) i)) atTop (𝓝 0) := by
  simpa only [← map_sub, productGradientLp_sub_localizedGradientLp, wCutoffErrorLp] using
    map_wCutoffErrorLp_tendsto_zero A χ i

end Burnett.CubicOffNull
