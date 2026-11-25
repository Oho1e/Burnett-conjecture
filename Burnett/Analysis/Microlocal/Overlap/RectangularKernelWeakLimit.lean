import Burnett.Analysis.Microlocal.Overlap.BoundedKernelWeakLimit

/-! Strong decay across two different windows and measures. -/
set_option autoImplicit false
set_option maxRecDepth 4100
set_option maxHeartbeats 4100000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Filter Set
open scoped ComplexConjugate InnerProduct Topology ENNReal

/-- A bounded measurable kernel between two finite-measure windows sends a
bounded weakly null input to a strongly null output, even when the spaces
and measures of the two windows differ. -/
theorem rectangularKernel_action_tendsto_zero
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [SFinite ν]
    (K : X → Y → ℂ) (hK : Measurable (uncurry K))
    (S : Set X) (T : Set Y) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hSfin : μ S ≠ ∞) (hTfin : ν T ≠ ∞)
    (hSupport : ∀ x y, x ∉ S ∨ y ∉ T → K x y = 0)
    (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ x y, ‖K x y‖ ≤ M)
    (f : ℕ → Y → ℂ) (hfm : ∀ n, Measurable (f n)) (hf : ∀ n, MemLp (f n) 2 ν)
    (B : ℝ) (hu : ∀ n, ‖(hf n).toLp (f n)‖ ≤ B)
    (hw : ∀ w : Lp ℂ 2 ν, Tendsto (fun n => inner ℂ w ((hf n).toLp (f n))) atTop (𝓝 0)) :
    ∃ hA : ∀ n, MemLp (fun x => ∫ y, K x y * f n y ∂ν) 2 μ,
      Tendsto (fun n => (hA n).toLp (fun x => ∫ y, K x y * f n y ∂ν)) atTop (𝓝 0) := by
  let A (n : ℕ) (x : X) := ∫ y, K x y * f n y ∂ν
  let g (x : X) (y : Y) := conj (K x y)
  let Q := T.indicator (fun _ : Y => M)
  have hQ : MemLp Q 2 ν := memLp_indicator_const 2 hT M (Or.inr hTfin)
  have hDom (x : X) (y : Y) : ‖g x y‖ ≤ ‖Q y‖ := by
    by_cases hy : y ∈ T
    · simpa only [g, Complex.norm_conj, Q, indicator_of_mem hy, Real.norm_of_nonneg hM] using hbound x y
    · simp only [g, hSupport x y (Or.inr hy), map_zero, norm_zero, Q, indicator_of_notMem hy, le_refl]
  have hG (x : X) : MemLp (g x) 2 ν := by
    have hGm : Measurable (g x) :=
      Complex.continuous_conj.measurable.comp (hK.comp (measurable_const.prodMk measurable_id))
    exact hQ.mono hGm.aestronglyMeasurable (Eventually.of_forall (hDom x))
  have hNorm (x : X) : ‖(hG x).toLp (g x)‖ ≤ ‖hQ.toLp Q‖ := by
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [(hG x).coeFn_toLp, hQ.coeFn_toLp] with y hy hy'
    rw [hy, hy']
    exact hDom x y
  have hPair (n : ℕ) (x : X) : A n x = inner ℂ ((hG x).toLp (g x)) ((hf n).toLp (f n)) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hG x).coeFn_toLp, (hf n).coeFn_toLp] with y hy hy'
    simp only [hy, hy', RCLike.inner_apply', g, Complex.conj_conj]
  have hPoint (x : X) : Tendsto (fun n => A n x) atTop (𝓝 0) := by
    simpa only [hPair] using hw ((hG x).toLp (g x))
  let D := ‖hQ.toLp Q‖ * B
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hu 0))
  have hBound n x : ‖A n x‖ ≤ S.indicator (fun _ => D) x := by
    by_cases hx : x ∈ S
    · rw [hPair, indicator_of_mem hx]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul (hNorm x) (hu n) (norm_nonneg _) (norm_nonneg _))
    · have hZero : A n x = 0 := by
        simp only [A, hSupport x _ (Or.inl hx), zero_mul, integral_zero]
      simp only [hZero, norm_zero, indicator_of_notMem hx, le_refl]
  have hA (n : ℕ) : MemLp (A n) 2 μ := by
    have hJoint : StronglyMeasurable (fun q : X × Y => K q.1 q.2 * f n q.2) :=
      (hK.mul ((hfm n).comp measurable_snd)).stronglyMeasurable
    refine (memLp_indicator_const 2 hS D (Or.inr hSfin)).mono
      (hJoint.integral_prod_right' (ν := ν)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    simpa only [norm_indicator_eq_indicator_norm, Real.norm_of_nonneg hD] using hBound n x
  have hBoundSq n x : ‖‖A n x‖ ^ 2‖ ≤ S.indicator (fun _ => D ^ 2) x := by
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx]
      exact pow_le_pow_left₀ (norm_nonneg _) (by simpa only [indicator_of_mem hx] using hBound n x) _
    · have hZero : ‖A n x‖ = 0 := le_antisymm
        (by simpa only [indicator_of_notMem hx] using hBound n x) (norm_nonneg _)
      simp [hZero, indicator_of_notMem hx]
  have hInt : Integrable (S.indicator (fun _ => D ^ 2)) μ :=
    (integrableOn_const hSfin).integrable_indicator hS
  have hLimit := tendsto_integral_of_dominated_convergence (μ := μ) (f := fun _ : X => (0 : ℝ)) _
    (fun n => (hA n).1.norm.pow 2) hInt
    (fun n => Eventually.of_forall (hBoundSq n))
    (Eventually.of_forall (fun x => by simpa using (hPoint x).norm.pow 2))
  have hSq (n : ℕ) : ‖(hA n).toLp (A n)‖ ^ 2 = ∫ x, ‖A n x‖ ^ 2 ∂μ := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def, ← integral_re (L2.integrable_inner _ _)]
    apply integral_congr_ae
    filter_upwards [(hA n).coeFn_toLp] with x hx
    rw [hx, ← norm_sq_eq_re_inner (𝕜 := ℂ)]
  refine ⟨hA, ?_⟩
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have ht : Tendsto (fun n => ‖(hA n).toLp (A n)‖ ^ 2) atTop (𝓝 0) := by
    simpa only [hSq, integral_zero] using hLimit
  simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp ht

end Burnett.Microlocal.Overlap
