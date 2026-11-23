import Burnett.Analysis.Microlocal.Overlap.DyadicKernelRemainder
import Burnett.Analysis.Microlocal.Overlap.DyadicKernelWeakLimit

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Function Set MeasureTheory Filter Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldMetric ManifoldBilinear
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.AngularDyadicKernel (E dyadicScale shellKernel shellKernel_hasFDerivAt)
open scoped ContDiff Manifold InnerProduct Topology ENNReal

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

/-- The localized difference of the pullback kernel and its affine approximation
on one dyadic shell. -/
def localizedOverlapShellDifference (c d : M) (K : Set E) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) (x y : E) : ℂ :=
  (K ×ˢ K).indicator
    (fun p => halfDensityKernelDifference (overlapTransition c d) (overlapJacobianWeight c d)
      (shellKernel m hm j) p.1 p.2) (x, y)

private theorem measurable_halfDensityKernelDifference
    (Φ : E → E) (w : E → ℝ) (k : E → ℂ)
    (hΦ : Measurable Φ) (hw : Measurable w) (hk : Measurable k) :
    Measurable (uncurry (halfDensityKernelDifference Φ w k)) := by
  have hEval : Continuous (fun p : (E →L[ℝ] E) × E => p.1 p.2) :=
    continuous_fst.clm_apply continuous_snd
  have hFrozen : Measurable (fun p : E × E => fderiv ℝ Φ p.1 (p.1 - p.2)) :=
    hEval.measurable.comp (((measurable_fderiv ℝ Φ).comp measurable_fst).prodMk
      (measurable_fst.sub measurable_snd))
  have hx : Measurable (fun p : E × E => w p.1) := hw.comp measurable_fst
  have hy : Measurable (fun p : E × E => w p.2) := hw.comp measurable_snd
  have hChange : Measurable (fun p : E × E => Φ p.1 - Φ p.2) :=
    (hΦ.comp measurable_fst).sub (hΦ.comp measurable_snd)
  exact ((hx.mul hy).smul (hk.comp hChange)).sub ((hx.pow_const 2).smul (hk.comp hFrozen))

theorem measurable_localizedOverlapShellDifference
    (c d : M) (K : Set E) (hK : MeasurableSet K) (m : BoundedSymbol E)
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E)) (j : ℕ) :
    Measurable (uncurry (localizedOverlapShellDifference c d K m hm j)) := by
  have hk : Continuous (shellKernel m hm j) :=
    continuous_iff_continuousAt.mpr fun x => (shellKernel_hasFDerivAt m hm j x).continuousAt
  exact (measurable_halfDensityKernelDifference _ _ _ (overlapTransition_measurable c d)
    (overlapJacobianWeight_measurable c d) hk.measurable).indicator (hK.prod hK)

variable [IsManifold Model ∞ M]

/-- On a compact convex overlap window, the series of actual half-density
shell-kernel differences gives a strongly null output for every bounded
weakly null sequence with integrable input representatives. -/
theorem exists_actualOverlapShell_actions_tendsto_zero
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c d : M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : ℕ → E → ℂ) (hfm : ∀ n, Measurable (f n)) (hf₁ : ∀ n, Integrable (f n))
    (hf : ∀ n, MemLp (f n) 2 volume)
    (C : ℝ) (hu : ∀ n, ‖(hf n).toLp (f n)‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((hf n).toLp (f n))) atTop (𝓝 0)) :
    ∃ U : ℕ → ℕ → ComplexL2 E,
      (∀ j n, U j n =ᵐ[volume] fun x =>
        ∫ y, localizedOverlapShellDifference c d K m hm j x y * f n y) ∧
      (∀ n, Summable (fun j => ‖U j n‖)) ∧
      Tendsto (fun n => ∑' j, U j n) atTop (𝓝 0) := by
  let R := localizedOverlapShellDifference c d K m hm
  have hKm := hK.isClosed.measurableSet
  obtain ⟨q, A, hq, hA, hEnv⟩ := overlap_shellKernel_uniform_envelope B hB hn c d K hK hKU hConv m hm
  have hSupp j (x y : E) (h : x ∉ K ∨ y ∉ K) : R j x y = 0 := by
    have hxy : (x,y) ∉ K ×ˢ K := fun hp => h.elim (fun hx => hx hp.1) (fun hy => hy hp.2)
    simp only [R, localizedOverlapShellDifference, indicator_of_notMem hxy]
  have hNorm j (x y : E) : ‖R j x y‖ ≤
      A * dyadicScale j ^ 3 / (1 + dyadicScale j * q * ‖x - y‖) ^ 5 := by
    by_cases hxy : (x,y) ∈ K ×ˢ K
    · simpa only [R, localizedOverlapShellDifference, indicator_of_mem hxy] using hEnv j x hxy.1 y hxy.2
    · simp only [R, localizedOverlapShellDifference, indicator_of_notMem hxy, norm_zero]
      have hs : 0 ≤ dyadicScale j := by unfold dyadicScale; positivity
      exact div_nonneg (mul_nonneg hA (pow_nonneg hs _))
        (pow_nonneg (add_nonneg zero_le_one (mul_nonneg (mul_nonneg hs hq.le) (norm_nonneg _))) _)
  exact exists_overlapShell_actions_tendsto_zero R
    (measurable_localizedOverlapShellDifference c d K hKm m hm) K hKm
    hK.measure_lt_top.ne hSupp A q hA hq hNorm f hfm hf₁ hf C hu hw

end Burnett.Microlocal.Overlap
