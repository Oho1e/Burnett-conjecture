import Burnett.Analysis.Cubic.FrequencyBounds
import Burnett.Analysis.Sobolev.TestJet
import Burnett.Analysis.Sobolev.L2Bounds

noncomputable section

namespace Burnett.CubicOffNull

open MeasureTheory Filter CubicExplicit CubicFrequencies
open X02.SobolevTestJet
open scoped Topology

abbrev Cutoff := X02.SobolevTestJet.D
abbrev Space := CubicExplicit.Space

def cutoffError (χ : Cutoff) (h : Space → ℝ) (i : Index) (x : Space) : ℝ :=
  directional i (χ : Space → ℝ) x * h x

/-- Actual product rule, without commuting the cutoff and a nonlocal map. -/
theorem cutoff_gradient_identity (χ : Cutoff) {h : Space → ℝ}
    (hh : Differentiable ℝ h) (i : Index) (x : Space) :
    CubicExplicit.D i (fun y => (χ : Space → ℝ) y * h y) x -
      (χ : Space → ℝ) x * CubicExplicit.D i h x = cutoffError χ h i x := by
  change (fderiv ℝ ((χ : Space → ℝ) * h) x) (basis i) - _ = _
  rw [fderiv_mul (test_differentiable χ x) (hh x)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  unfold cutoffError CubicExplicit.D directional
  change (χ : Space → ℝ) x * fderiv ℝ h x (basis i) +
    h x * fderiv ℝ (χ : Space → ℝ) x (basis i) -
    (χ : Space → ℝ) x * fderiv ℝ h x (basis i) =
    fderiv ℝ (χ : Space → ℝ) x (basis i) * h x
  ring

theorem cutoffError_memLp (χ : Cutoff) {h : Space → ℝ} (hh : Continuous h) (i : Index) :
    MemLp (cutoffError χ h i) 2 (volume : Measure Space) :=
  ((directional_continuous i χ).mul hh).memLp_of_hasCompactSupport
    ((directional_compactSupport i χ).mul_right)

theorem cutoffError_abs_le (χ : Cutoff) {h : Space → ℝ} {C : ℝ}
    (hh : ∀ x, |h x| ≤ C) (i : Index) (x : Space) :
    |cutoffError χ h i x| ≤ C * |directional i (χ : Space → ℝ) x| := by
  rw [cutoffError, abs_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hh x) (abs_nonneg _)

def fCutoffErrorLp (χ : Cutoff) (n : ℕ) (i : Index) : ScalarL2 :=
  (cutoffError_memLp χ (fSequence_smooth n).continuous i).toLp
    (cutoffError χ (fSequence n) i)

def wCutoffErrorLp (χ : Cutoff) (n : ℕ) (i : Index) : ScalarL2 :=
  (cutoffError_memLp χ (wSequence_smooth n).continuous i).toLp
    (cutoffError χ (wSequence n) i)

theorem fCutoffErrorLp_tendsto_zero (χ : Cutoff) (i : Index) :
    Tendsto (fun n => fCutoffErrorLp χ n i) atTop (𝓝 0) :=
  X02.L2Bounds.toLp_tendsto_zero_of_bound
    (fun n => cutoffError_memLp χ (fSequence_smooth n).continuous i)
    (directional_memLp i χ) (fun n => inv_nonneg.mpr (N_pos n).le)
    tendsto_inv_N_zero (fun n x => cutoffError_abs_le χ (fSequence_abs_le_inv_N n) i x)

theorem wCutoffErrorLp_tendsto_zero (χ : Cutoff) (i : Index) :
    Tendsto (fun n => wCutoffErrorLp χ n i) atTop (𝓝 0) :=
  X02.L2Bounds.toLp_tendsto_zero_of_bound
    (fun n => cutoffError_memLp χ (wSequence_smooth n).continuous i)
    (directional_memLp i χ) (fun n => inv_nonneg.mpr (N_pos n).le)
    tendsto_inv_N_zero (fun n x => cutoffError_abs_le χ (wSequence_abs_le_inv_N n) i x)

/-- The product-rule error remains small after any fixed continuous linear
operator on L². A Fourier multiplier can consume this only after its actual
L² boundedness has been constructed. -/
theorem map_fCutoffErrorLp_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : ScalarL2 →L[ℝ] E) (χ : Cutoff) (i : Index) :
    Tendsto (fun n => A (fCutoffErrorLp χ n i)) atTop (𝓝 0) := by
  simpa only [map_zero] using A.continuous.tendsto 0 |>.comp (fCutoffErrorLp_tendsto_zero χ i)

theorem map_wCutoffErrorLp_tendsto_zero {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (A : ScalarL2 →L[ℝ] E) (χ : Cutoff) (i : Index) :
    Tendsto (fun n => A (wCutoffErrorLp χ n i)) atTop (𝓝 0) := by
  simpa only [map_zero] using A.continuous.tendsto 0 |>.comp (wCutoffErrorLp_tendsto_zero χ i)

end Burnett.CubicOffNull
