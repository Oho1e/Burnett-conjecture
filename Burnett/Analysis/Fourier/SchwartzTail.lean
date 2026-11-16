import Mathlib.Analysis.Distribution.FourierSchwartz
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Squared Fourier tails for a fixed Schwartz function, on the whole space.
This file uses the actual `exp (-2π i ⟪x,ξ⟫)` Fourier integral. It does not
assume or construct an L² Fourier extension. -/

noncomputable section

namespace Burnett.Fourier

open MeasureTheory Filter
open scoped FourierTransform Topology

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]

theorem schwartz_norm_sq_integrable (f : SchwartzMap V ℂ) :
    Integrable (fun ξ => ‖f ξ‖^2) (volume : Measure V) := by
  refine (f.integrable.norm.const_mul ((SchwartzMap.seminorm ℂ 0 0) f)).mono'
    (f.continuous.norm.pow 2).aestronglyMeasurable ?_
  filter_upwards with ξ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hb := mul_le_mul_of_nonneg_right (f.norm_le_seminorm ℂ ξ) (norm_nonneg (f ξ))
  nlinarith

theorem fourier_norm_sq_integrable (f : SchwartzMap V ℂ) :
    Integrable (fun ξ => ‖𝓕 (f : V → ℂ) ξ‖^2) (volume : Measure V) :=
  schwartz_norm_sq_integrable (SchwartzMap.fourierTransformCLM ℂ f)

/-- Arbitrary measurable regions escaping every fixed point consume zero
energy of a fixed L² density. This is dominated convergence, without any
compact support restriction on the regions. -/
theorem integral_indicator_norm_sq_tendsto_zero
    {g : V → ℂ} (hg : Integrable (fun ξ => ‖g ξ‖^2) (volume : Measure V))
    {S : ℕ → Set V} (hS : ∀ n, MeasurableSet (S n))
    (hescape : ∀ ξ, ∀ᶠ n in atTop, ξ ∉ S n) :
    Tendsto (fun n => ∫ ξ, (S n).indicator (fun η => ‖g η‖^2) ξ)
      atTop (𝓝 0) := by
  have ht := tendsto_integral_filter_of_dominated_convergence (f := fun _ : V => (0 : ℝ))
    (fun ξ => ‖g ξ‖^2)
    (Eventually.of_forall (fun n => hg.aestronglyMeasurable.indicator (hS n)))
    (Eventually.of_forall (fun n => Eventually.of_forall (fun ξ => by
      by_cases h : ξ ∈ S n
      · simp only [Set.indicator_of_mem h, Real.norm_of_nonneg (sq_nonneg _), le_refl]
      · simp only [Set.indicator_of_notMem h, norm_zero]; positivity)))
    hg
    (Eventually.of_forall (fun ξ => tendsto_const_nhds.congr' (by
      filter_upwards [hescape ξ] with n hn
      simp [Set.indicator_of_notMem hn])))
  simpa only [integral_zero] using ht

/-- The full squared Fourier tail outside radii tending to infinity. -/
theorem fourier_tail_tendsto_zero (f : SchwartzMap V ℂ) {R : ℕ → ℝ}
    (hR : Tendsto R atTop atTop) :
    Tendsto (fun n => ∫ ξ in {η : V | R n ≤ ‖η‖}, ‖𝓕 (f : V → ℂ) ξ‖^2)
      atTop (𝓝 0) := by
  have hS (n : ℕ) : MeasurableSet {η : V | R n ≤ ‖η‖} :=
    isClosed_le continuous_const continuous_norm |>.measurableSet
  have ht := integral_indicator_norm_sq_tendsto_zero (fourier_norm_sq_integrable f) hS
    (fun ξ => by
      filter_upwards [hR.eventually (Ioi_mem_atTop ‖ξ‖)] with n hn
      exact not_le.mpr hn)
  simpa only [integral_indicator (hS _)] using ht

end Burnett.Fourier
