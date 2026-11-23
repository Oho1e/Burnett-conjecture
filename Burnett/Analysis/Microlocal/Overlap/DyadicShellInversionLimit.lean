import Burnett.Analysis.Microlocal.Overlap.FiniteConjugationWeakLimit
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

set_option autoImplicit false
set_option maxHeartbeats 2100000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel
open scoped ContDiff FourierTransform Topology InnerProduct

/-- The finite angular cutoff can be removed in the inverse Fourier integral
against any integrable frequency input, including after a fixed change of covector. -/
theorem tendsto_inverseFourier_partialAngular_comp
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (L : E → E) (hL : Measurable L) (f : E → ℂ) (hf : Integrable f) (x : E) :
    Tendsto (fun N => (𝓕⁻ (fun ξ => partialAngularSymbol m N (L ξ) * f ξ)) x) atTop
      (𝓝 ((𝓕⁻ (fun ξ => normalizedAngularSymbol m (L ξ) * f ξ)) x)) := by
  have hmM : Measurable (m : E → ℂ) := measurable_of_continuousOn_compl_singleton 0 hm.continuousOn
  have hCore (s : ℝ) : Measurable (boundedRadialCore s : E → ℂ) :=
    Complex.continuous_ofReal.measurable.comp
      (radialCore_contDiff.continuous.comp (continuous_const.smul continuous_id)).measurable
  have hPN (N : ℕ) : Measurable (partialAngularSymbol m N : E → ℂ) :=
    ((hCore (dyadicScale N)⁻¹).sub (hCore 1)).mul hmM
  let phase (ξ : E) : ℂ := Complex.exp ((↑(2 * Real.pi * inner ℝ ξ x) : ℂ) * Complex.I)
  have hPhase : Continuous phase := Complex.continuous_exp.comp (by fun_prop)
  have hPNBound (N : ℕ) (ξ : E) : ‖partialAngularSymbol m N (L ξ)‖ ≤ 2 * m.bound := by
    have h := (partialAngularSymbol m N).norm_le (L ξ)
    change ‖partialAngularSymbol m N (L ξ)‖ ≤ (1 + 1) * m.bound at h
    norm_num at h
    exact h
  simp only [Real.fourierIntegralInv_eq', smul_eq_mul]
  apply tendsto_integral_of_dominated_convergence (fun ξ => 2 * m.bound * ‖f ξ‖)
  · intro N
    exact hPhase.aestronglyMeasurable.mul (((hPN N).comp hL).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  · exact hf.norm.const_mul _
  · intro N
    filter_upwards with ξ
    simp only [norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_right (hPNBound N ξ) (norm_nonneg _)
  · filter_upwards with ξ
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [partialAngularSymbol_eventually_eq m (L ξ)] with N hN
    change partialAngularSymbol m N (L ξ) = normalizedAngularSymbol m (L ξ) at hN
    rw [hN]

/-- Pointwise limits of actual representatives identify the limit in L². -/
theorem ae_eq_of_tendsto_L2_and_pointwise
    (F : ℕ → ComplexL2 E) (u : ComplexL2 E) (f : ℕ → E → ℂ) (v : E → ℂ)
    (hEq : ∀ N, (F N : E → ℂ) =ᵐ[volume] f N)
    (hL : Tendsto F atTop (𝓝 u)) (hPoint : ∀ x, Tendsto (fun N => f N x) atTop (𝓝 (v x))) :
    (u : E → ℂ) =ᵐ[volume] v := by
  obtain ⟨s, hs, hAE⟩ := (tendstoInMeasure_of_tendsto_Lp hL).exists_seq_tendsto_ae
  have hAll : ∀ᵐ x ∂(volume : Measure E), ∀ N, F N x = f N x := ae_all_iff.mpr hEq
  filter_upwards [hAE, hAll] with x hx hSame
  apply tendsto_nhds_unique hx
  have hLim := (hPoint x).comp hs.tendsto_atTop
  simpa only [Function.comp_def, hSame] using hLim

end Burnett.Microlocal.Overlap
