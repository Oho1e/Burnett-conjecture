import Burnett.Analysis.Microlocal.Overlap.DyadicSchur
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Filter Set Burnett.Fourier
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ComplexConjugate InnerProduct Topology ENNReal

/-- A bounded kernel supported in a finite-volume rectangle takes bounded
weakly null sequences to strongly null sequences. -/
theorem boundedKernel_action_tendsto_zero
    (K : E → E → ℂ) (hK : Measurable (uncurry K))
    (S : Set E) (hS : MeasurableSet S) (hSfin : (volume : Measure E) S ≠ ∞)
    (hSupport : ∀ x y, x ∉ S ∨ y ∉ S → K x y = 0)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x y, ‖K x y‖ ≤ M)
    (f : ℕ → E → ℂ) (hf : ∀ n, MemLp (f n) 2 volume)
    (B : ℝ) (hu : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((hf n).toLp (f n))) atTop (𝓝 0))
    (hA : ∀ n, MemLp (fun x => ∫ y, K x y * f n y) 2 volume) :
    Tendsto (fun n => (hA n).toLp (fun x => ∫ y, K x y * f n y)) atTop (𝓝 0) := by
  let A (n : ℕ) (x : E) := ∫ y, K x y * f n y
  let g (x y : E) := conj (K x y)
  let Q := S.indicator (fun _ : E => M)
  have hQ : MemLp Q 2 volume := memLp_indicator_const 2 hS M (Or.inr hSfin)
  have hGm (x : E) : Measurable (g x) :=
    Complex.continuous_conj.measurable.comp (hK.comp (measurable_const.prodMk measurable_id))
  have hDom (x y : E) : ‖g x y‖ ≤ ‖Q y‖ := by
    by_cases hy : y ∈ S
    · simpa only [g, Complex.norm_conj, Q, indicator_of_mem hy, Real.norm_of_nonneg hM] using hbound x y
    · simp only [g, hSupport x y (Or.inr hy), map_zero, norm_zero, Q, indicator_of_notMem hy, le_refl]
  have hG (x : E) : MemLp (g x) 2 volume :=
    hQ.mono (hGm x).aestronglyMeasurable (Eventually.of_forall (hDom x))
  have hNorm (x : E) : ‖(hG x).toLp (g x)‖ ≤ ‖hQ.toLp Q‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hG x).coeFn_toLp, hQ.coeFn_toLp] with y hy hy'
    rw [hy, hy']
    exact hDom x y
  have hPair (n : ℕ) (x : E) : A n x = inner ℂ ((hG x).toLp (g x)) ((hf n).toLp (f n)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hG x).coeFn_toLp, (hf n).coeFn_toLp] with y hy hy'
    simp only [hy, hy', RCLike.inner_apply', g, Complex.conj_conj]
  have hPoint (x : E) : Tendsto (fun n => A n x) atTop (𝓝 0) := by
    simpa only [hPair] using hw ((hG x).toLp (g x))
  let D := ‖hQ.toLp Q‖ * B
  have hBound n x : ‖‖A n x‖ ^ 2‖ ≤ S.indicator (fun _ => D ^ 2) x := by
    by_cases hx : x ∈ S
    · have hN : ‖A n x‖ ≤ D := by
        rw [hPair]
        exact (norm_inner_le_norm _ _).trans (mul_le_mul (hNorm x) (hu n) (norm_nonneg _)
          (norm_nonneg _))
      rw [Real.norm_of_nonneg (sq_nonneg _), indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) hN _
    · have hZ : A n x = 0 := by
        simp only [A, hSupport x _ (Or.inl hx), zero_mul, integral_zero]
      simp [hZ, indicator_of_notMem hx]
  have hInt : Integrable (S.indicator (fun _ => D ^ 2)) :=
    (integrableOn_const hSfin).integrable_indicator hS
  have hT := tendsto_integral_of_dominated_convergence (f := fun _ : E => (0 : ℝ)) _
    (fun n => (hA n).1.norm.pow 2) hInt
    (fun n => Eventually.of_forall (hBound n))
    (Eventually.of_forall (fun x => by simpa using (hPoint x).norm.pow 2))
  have hSq (n : ℕ) : ‖(hA n).toLp (A n)‖ ^ 2 = ∫ x, ‖A n x‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [(hA n).coeFn_toLp] with x hx
    rw [hx, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun n => ‖(hA n).toLp (A n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hSq, integral_zero] using hT
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp ht

end Burnett.Microlocal.Overlap
