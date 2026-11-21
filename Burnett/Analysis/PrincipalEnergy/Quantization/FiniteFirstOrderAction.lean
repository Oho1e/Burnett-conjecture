import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderDyadic
import Burnett.Analysis.PrincipalEnergy.Quantization.LipschitzKernel

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Filter Function MeasureTheory Set Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators FourierTransform Topology

def firstOrderFiniteSymbol (a : E → E → ℂ) (x : E) (N : ℕ) (ξ : E) : ℂ :=
  ∑ j ∈ Finset.range N, (annulus ((dyadicScale j)⁻¹ • ξ) : ℂ) * a x ξ

private theorem outer_scale (N : ℕ) (ξ : E) :
    (1 / 2 : ℝ) • ((dyadicScale N)⁻¹ • ξ) = (dyadicScale (N + 1))⁻¹ • ξ := by
  rw [smul_smul]
  congr 1
  unfold dyadicScale
  rw [pow_succ]
  field_simp

/-- The same annuli use the original symbol and one outer cutoff.
There is no replacement by a homogeneous angular part. -/
theorem firstOrderFiniteSymbol_telescope (a : E → E → ℂ) (x : E) (N : ℕ) (ξ : E) :
    firstOrderFiniteSymbol a x N ξ =
      ((radialCore ((dyadicScale N)⁻¹ • ξ) - radialCore ξ : ℝ) : ℂ) * a x ξ := by
  unfold firstOrderFiniteSymbol
  induction N with
  | zero => simp [dyadicScale]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, annulus, outer_scale]
    push_cast
    ring

private theorem shell_frequency_compact {a : E → E → ℂ} (x : E) (j : ℕ) :
    HasCompactSupport (fun ξ => (annulus ((dyadicScale j)⁻¹ • ξ) : ℂ) * a x ξ) := by
  have hs : 0 < dyadicScale j := by unfold dyadicScale; positivity
  apply (isCompact_closedBall (0 : E) (4 * dyadicScale j)).of_isClosed_subset isClosed_closure
  apply closure_minimal _ Metric.isClosed_closedBall
  intro ξ hξ
  by_contra! hFar
  have hSize : 4 * dyadicScale j < ‖ξ‖ := by
    simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hFar
  have hAnnulus : 4 ≤ ‖(dyadicScale j)⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr hs.le), ← div_eq_inv_mul]
    exact (le_div_iff₀ hs).mpr hSize.le
  exact hξ (by simp [annulus_eq_zero_far _ hAnnulus])

private theorem shell_frequency_continuous {a : E → E → ℂ} (x : E) (h : Continuous (a x)) (j : ℕ) :
    Continuous (fun ξ => (annulus ((dyadicScale j)⁻¹ • ξ) : ℂ) * a x ξ) :=
  (Complex.continuous_ofReal.comp
    (annulus_contDiff.continuous.comp (continuous_const.smul continuous_id))).mul h

private theorem shell_frequency_integrable {a : E → E → ℂ} (x : E) (h : Continuous (a x)) (j : ℕ) :
    Integrable (fun ξ => (annulus ((dyadicScale j)⁻¹ • ξ) : ℂ) * a x ξ) (volume : Measure E) :=
  (shell_frequency_continuous x h j).integrable_of_hasCompactSupport (shell_frequency_compact x j)

theorem inverseFourier_firstOrderFiniteSymbol (a : E → E → ℂ) (x : E) (h : Continuous (a x))
    (N : ℕ) (z : E) :
    𝓕⁻ (firstOrderFiniteSymbol a x N) z =
      ∑ j ∈ Finset.range N, firstOrderAnnularKernel a x j z := by
  simp only [firstOrderFiniteSymbol, firstOrderAnnularKernel, Real.fourierIntegralInv_eq, Finset.smul_sum]
  apply integral_finset_sum
  intro j _
  have hChar : Continuous (fun ξ : E => Real.fourierChar (inner ℝ ξ z)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  exact (shell_frequency_integrable x h j).mono
    (hChar.aestronglyMeasurable.smul (shell_frequency_integrable x h j).1) (Eventually.of_forall fun ξ => by
      rw [Circle.norm_smul])

def firstOrderFiniteAction (a : E → E → ℂ) (N : ℕ) (f : E → ℂ) (x : E) : ℂ :=
  𝓕⁻ (fun ξ => firstOrderFiniteSymbol a x N ξ * (𝓕 f) ξ) x

private theorem firstOrderFiniteSymbol_integrable (a : E → E → ℂ) (x : E) (h : Continuous (a x))
    (N : ℕ) : Integrable (firstOrderFiniteSymbol a x N) (volume : Measure E) :=
  integrable_finset_sum _ (fun j _ => shell_frequency_integrable x h j)

theorem firstOrderFiniteAction_eq_kernel (a : E → E → ℂ) (x : E) (h : Continuous (a x))
    (N : ℕ) (f : E → ℂ) (hf : Integrable f (volume : Measure E)) :
    firstOrderFiniteAction a N f x = ∫ y,
      (∑ j ∈ Finset.range N, firstOrderAnnularKernel a x j (x-y)) * f y := by
  unfold firstOrderFiniteAction
  rw [inverseFourier_mul_fourier_eq_convolution _ _ (firstOrderFiniteSymbol_integrable a x h N) hf]
  simp only [inverseFourier_firstOrderFiniteSymbol a x h]

/-- The term with `r x - r y` has the exact sign of `M_r B_N - B_N M_r`.
Continuity and compact support ensure genuine Bochner integrability for these tests. -/
theorem firstOrderFiniteCoefficientCommutator_eq_kernel (a : E → E → ℂ) (x : E) (h : Continuous (a x))
    (N : ℕ) (r f : E → ℂ) (hr : Continuous r) (hf : Continuous f) (hfC : HasCompactSupport f) :
    r x * firstOrderFiniteAction a N f x - firstOrderFiniteAction a N (fun y => r y * f y) x =
      ∫ y, coefficientKernel r (fun u z => ∑ j ∈ Finset.range N, firstOrderAnnularKernel a u j z) x y * f y := by
  let k (y : E) := ∑ j ∈ Finset.range N, firstOrderAnnularKernel a x j (x-y)
  have hk : Continuous k := by
    rw [show k = fun y => 𝓕⁻ (firstOrderFiniteSymbol a x N) (x-y) from
      funext fun y => (inverseFourier_firstOrderFiniteSymbol a x h N (x-y)).symm]
    rw [show (fun y : E => 𝓕⁻ (firstOrderFiniteSymbol a x N) (x-y)) =
      fun y => 𝓕 (firstOrderFiniteSymbol a x N) (-(x-y)) from
      funext fun y => Real.fourierIntegralInv_eq_fourierIntegral_neg _ _]
    have hF : Continuous (𝓕 (firstOrderFiniteSymbol a x N)) := by
      unfold Real.fourierIntegral
      exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
        (continuous_fst.inner continuous_snd) (firstOrderFiniteSymbol_integrable a x h N)
    exact hF.comp (continuous_const.sub continuous_id).neg
  have hrf : Integrable (fun y => r y * f y) (volume : Measure E) :=
    (hr.mul hf).integrable_of_hasCompactSupport hfC.mul_left
  rw [firstOrderFiniteAction_eq_kernel a x h N f (hf.integrable_of_hasCompactSupport hfC),
    firstOrderFiniteAction_eq_kernel a x h N _ hrf]
  change r x * (∫ y, k y * f y) - (∫ y, k y * (r y * f y)) = _
  have hi₁ : Integrable (fun y => r x * (k y * f y)) (volume : Measure E) :=
    (continuous_const.mul (hk.mul hf)).integrable_of_hasCompactSupport hfC.mul_left.mul_left
  have hi₂ : Integrable (fun y => k y * (r y * f y)) (volume : Measure E) :=
    (hk.mul (hr.mul hf)).integrable_of_hasCompactSupport hfC.mul_left.mul_left
  rw [← integral_const_mul, ← integral_sub hi₁ hi₂]
  apply integral_congr_ae
  filter_upwards with y
  change r x * (k y * f y) - k y * (r y * f y) = (r x - r y) * k y * f y
  ring

end Burnett.Analysis.FirstOrderDyadic
