import Burnett.Analysis.Microlocal.Overlap.RectangularKernelWeakLimit

/-! Pairing across two compact coordinate windows without a common scalarization. -/
set_option autoImplicit false
set_option maxRecDepth 4200
set_option maxHeartbeats 4800000

noncomputable section
namespace Burnett.Microlocal.Overlap

open Function MeasureTheory Filter Set
open scoped ComplexConjugate InnerProduct Topology ENNReal

/-- A continuous kernel on the compact rectangle itself gives a zero
bilinear limit from the weakly null input against any bounded output test.
The coordinate windows may have unrelated measures and ambient spaces. -/
theorem continuous_compactRectangle_kernelPairing_tendsto_zero
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] [SFinite ν]
    (S : Set X) (T : Set Y) (hS : IsCompact S) (hT : IsCompact T)
    (K : X → Y → ℂ) (hK : ContinuousOn (uncurry K) (S ×ˢ T))
    (u : ℕ → Y → ℂ) (hum : ∀ n, Measurable (u n)) (hu : ∀ n, MemLp (u n) 2 ν)
    (v : ℕ → X → ℂ) (hv : ∀ n, MemLp (v n) 2 μ)
    (B C : ℝ) (hB : ∀ n, ‖(hu n).toLp (u n)‖ ≤ B) (hC : ∀ n, ‖(hv n).toLp (v n)‖ ≤ C)
    (hw : ∀ w : Lp ℂ 2 ν, Tendsto (fun n => inner ℂ w ((hu n).toLp (u n))) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in S, conj (v n x) * (∫ y in T, K x y * u n y ∂ν) ∂μ) atTop (𝓝 0) := by
  classical
  let R := S ×ˢ T
  let k (x : X) (y : Y) := R.indicator (uncurry K) (x, y)
  have hMeas : Measurable (uncurry k) := by
    have hm := hK.measurable_piecewise (g := fun _ : X × Y => (0 : ℂ)) continuous_const.continuousOn
      (hS.measurableSet.prod hT.measurableSet)
    simpa only [uncurry, k, R, Set.indicator, Set.piecewise] using hm
  obtain ⟨D, hD⟩ := (hS.prod hT).exists_bound_of_continuousOn hK
  have hSupport (x : X) (y : Y) (h : x ∉ S ∨ y ∉ T) : k x y = 0 := by
    have hOutside : (x, y) ∉ R := not_and_or.mpr h
    exact indicator_of_notMem hOutside _
  have hBound (x : X) (y : Y) : ‖k x y‖ ≤ max D 0 := by
    by_cases h : (x, y) ∈ R
    · simpa only [k, indicator_of_mem h] using (hD (x, y) h).trans (le_max_left D 0)
    · simp only [k, indicator_of_notMem h, norm_zero, le_max_right]
  obtain ⟨hAction, hLimit⟩ := rectangularKernel_action_tendsto_zero μ ν k hMeas S T
    hS.measurableSet hT.measurableSet hS.measure_lt_top.ne hT.measure_lt_top.ne hSupport
    (max D 0) (le_max_right _ _) hBound u hum hu B hB hw
  let z n := (hAction n).toLp (fun x => ∫ y, k x y * u n y ∂ν)
  have hPair n : inner ℂ ((hv n).toLp (v n)) (z n) =
      ∫ x in S, conj (v n x) * (∫ y in T, K x y * u n y ∂ν) ∂μ := by
    rw [L2.inner_def, ← integral_indicator hS.measurableSet]
    apply integral_congr_ae
    filter_upwards [(hv n).coeFn_toLp, (hAction n).coeFn_toLp] with x hvx hzx
    rw [RCLike.inner_apply', hvx, show z n x = _ from hzx]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem hx, ← integral_indicator hT.measurableSet]
      congr 1
      apply integral_congr_ae
      filter_upwards with y
      by_cases hy : y ∈ T
      · rw [show k x y = K x y from indicator_of_mem (show (x, y) ∈ R from ⟨hx, hy⟩) _,
          indicator_of_mem hy]
      · simp only [hSupport x y (Or.inr hy), zero_mul, indicator_of_notMem hy]
    · simp only [hSupport x _ (Or.inl hx), zero_mul, integral_zero, mul_zero, indicator_of_notMem hx]
  simp_rw [← hPair]
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hNormLimit := (tendsto_const_nhds (x := C)).mul hLimit.norm
  rw [norm_zero, mul_zero] at hNormLimit
  exact squeeze_zero (fun _ => norm_nonneg _) (fun n => (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right (hC n) (norm_nonneg _))) hNormLimit

end Burnett.Microlocal.Overlap
