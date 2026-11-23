import Burnett.Analysis.Microlocal.Overlap.FrozenShellSymbol
import Burnett.Analysis.Microlocal.Overlap.KernelRemainder

set_option autoImplicit false
set_option maxHeartbeats 1100000

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open MeasureTheory Set Burnett.Fourier
open Burnett.Analysis.CapFourier (pullbackSchwartz pullbackSchwartz_apply)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open scoped BigOperators ContDiff FourierTransform Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The conjugation formula for an actual Fourier product on the
compact-window transported input. -/
theorem overlap_fourier_kernel_conjugation
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (p f : E → ℂ) (hp : Integrable p) (hf : Continuous f) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => p ξ * (𝓕 g) ξ)) (Φ x) =
      ∫ y in K, ((w x * w y) • (𝓕⁻ p) (Φ x - Φ y)) * f y := by
  intro Φ w g
  rw [inverseFourier_mul_fourier_eq_convolution p g hp
    (integrable_transportedHalfDensity c d K hK hKU hf)]
  exact overlap_kernel_conjugation c d K hK hKU (𝓕⁻ p) f x

/-- The actual finite angular Fourier action on the target field, pulled
back to the source window at the same finite cutoff index. -/
theorem overlap_partialAngularFourier_conjugation
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) =
      ∫ y in K, ((w x * w y) • partialAngularKernel m hm N (Φ x - Φ y)) * f y := by
  have hp : Integrable (partialAngularSymbol m N : E → ℂ) := by
    rw [← show (partialAngularSchwartz m hm N : E → ℂ) = (partialAngularSymbol m N : E → ℂ) from
      funext (partialAngularSchwartz_apply m hm hd N)]
    exact (partialAngularSchwartz m hm N).integrable
  simpa only [inverseFourier_partialAngular_eq_sum m hm hd, partialAngularKernel] using
    overlap_fourier_kernel_conjugation c d K hK hKU (partialAngularSymbol m N) f hp hf x

/-- The variable frequency transform is held fixed at the output point
when evaluating its Fourier action on the source-window field. -/
theorem overlap_frozen_partialAngular_convolution
    (c d : M) (K : Set E) (hK : IsCompact K) {x : E} (hx : x ∈ (chartTransition c d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let p (ξ : E) := partialAngularSymbol m N (frozenChartFrequency c d hx ξ)
    let A := fderiv ℝ (overlapTransition c d) x
    let w := overlapJacobianWeight c d
    (𝓕⁻ (fun ξ => p ξ * (𝓕 (K.indicator f)) ξ)) x =
      ∫ y in K, ((w x)^2 • partialAngularKernel m hm N (A (x-y))) * f y := by
  intro p A w
  let p₀ := pullbackSchwartz (frozenChartFrequency c d hx) (partialAngularSchwartz m hm N)
  have hep : (p₀ : E → ℂ) = p := by
    funext ξ
    rw [pullbackSchwartz_apply]
    exact partialAngularSchwartz_apply m hm hd N _
  have hp : Integrable p := hep ▸ p₀.integrable
  have hfi : Integrable (K.indicator f) :=
    (hf.continuousOn.integrableOn_compact hK).integrable_indicator hK.measurableSet
  rw [inverseFourier_mul_fourier_eq_convolution p (K.indicator f) hp hfi]
  have hCut :
      (fun y => (𝓕⁻ p) (x-y) * K.indicator f y) =
        K.indicator (fun y => (𝓕⁻ p) (x-y) * f y) := by
    funext y
    by_cases hy : y ∈ K
    · simp only [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, mul_zero]
  rw [hCut, integral_indicator hK.measurableSet]
  apply integral_congr_ae
  filter_upwards with y
  rw [← overlap_frozen_partialAngularKernel_symbol c d hx m hm hd N (x-y)]

theorem overlap_partialAngularFourier_difference
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    {x : E} (hx : x ∈ (chartTransition c d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d hx ξ) *
        (𝓕 (K.indicator f)) ξ)) x =
      ∫ y in K, halfDensityKernelDifference Φ w (partialAngularKernel m hm N) x y * f y := by
  intro Φ w g
  let k := partialAngularKernel m hm N
  let A := fderiv ℝ Φ x
  have hk : Continuous k :=
    continuous_iff_continuousAt.mpr fun z => (partialAngularKernel_hasFDerivAt m hm N z).continuousAt
  have hΦ : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hw : ContinuousOn w K := (overlapJacobianWeight_continuousOn c d).mono hKU
  have h₁ : ContinuousOn (fun y => ((w x * w y) • k (Φ x - Φ y)) * f y) K :=
    ((continuousOn_const.mul hw).smul
      (hk.comp_continuousOn (continuousOn_const.sub hΦ))).mul hf.continuousOn
  have h₂ : Continuous (fun y => ((w x)^2 • k (A (x-y))) * f y) :=
    (continuous_const.smul (hk.comp (A.continuous.comp (continuous_const.sub continuous_id)))).mul hf
  rw [overlap_partialAngularFourier_conjugation c d K hK hKU m hm hd N f hf x,
    overlap_frozen_partialAngular_convolution c d K hK hx m hm hd N f hf,
    ← integral_sub (h₁.integrableOn_compact hK) (h₂.continuousOn.integrableOn_compact hK)]
  simp only [halfDensityKernelDifference, sub_mul, A, k]

/-- On the compact output window the difference is exactly the finite
sum of the product-window-localized single-shell differences. -/
theorem overlap_partialAngularFourier_difference_localized
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    {x : E} (hx : x ∈ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x =
      ∫ y, (∑ j ∈ Finset.range N, (K ×ˢ K).indicator
        (fun Pair => halfDensityKernelDifference Φ w (shellKernel m hm j) Pair.1 Pair.2)
        (x, y)) * f y := by
  intro Φ w g
  let R (y : E) := halfDensityKernelDifference Φ w (partialAngularKernel m hm N) x y * f y
  rw [overlap_partialAngularFourier_difference c d K hK hKU (hKU hx) m hm hd N f hf]
  rw [← integral_indicator hK.measurableSet]
  apply integral_congr_ae
  filter_upwards with y
  change K.indicator R y = _
  by_cases hy : y ∈ K
  · simp only [indicator_of_mem hy, indicator_of_mem (show (x,y) ∈ K ×ˢ K from ⟨hx, hy⟩),
      R, halfDensityKernelDifference, partialAngularKernel, Finset.smul_sum, Finset.sum_sub_distrib]
  · have hy' : (x,y) ∉ K ×ˢ K := fun h => hy h.2
    simp only [indicator_of_notMem hy, indicator_of_notMem hy', Finset.sum_const_zero, zero_mul]

/-- The same finite difference as a sum of the individual shell actions,
in the order needed for the corresponding finite sum of L² elements. -/
theorem overlap_partialAngularFourier_difference_sum_actions
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    {x : E} (hx : x ∈ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (N : ℕ) (f : E → ℂ) (hf : Continuous f) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let g := transportedHalfDensity c d K f
    w x • (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 g) ξ)) (Φ x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x =
      ∑ j ∈ Finset.range N, ∫ y, (K ×ˢ K).indicator
        (fun p => halfDensityKernelDifference Φ w (shellKernel m hm j) p.1 p.2)
        (x, y) * f y := by
  intro Φ w g
  rw [overlap_partialAngularFourier_difference_localized c d K hK hKU hx m hm hd N f hf]
  simp only [Finset.sum_mul]
  apply integral_finset_sum
  intro j _
  let k := shellKernel m hm j
  let A := fderiv ℝ Φ x
  let H (y : E) := halfDensityKernelDifference Φ w k x y * f y
  have hk : Continuous k :=
    continuous_iff_continuousAt.mpr fun z => (shellKernel_hasFDerivAt m hm j z).continuousAt
  have hΦ : ContinuousOn Φ K := (overlapTransition_contDiffOn c d).continuousOn.mono hKU
  have hw : ContinuousOn w K := (overlapJacobianWeight_continuousOn c d).mono hKU
  have hActual : ContinuousOn (fun y => (w x * w y) • k (Φ x - Φ y)) K :=
    (continuousOn_const.mul hw).smul (hk.comp_continuousOn (continuousOn_const.sub hΦ))
  have hFrozen : Continuous (fun y => (w x)^2 • k (A (x-y))) :=
    continuous_const.smul (hk.comp (A.continuous.comp (continuous_const.sub continuous_id)))
  have hH : ContinuousOn H K := (hActual.sub hFrozen.continuousOn).mul hf.continuousOn
  have hCut : (fun y => (K ×ˢ K).indicator
      (fun p => halfDensityKernelDifference Φ w k p.1 p.2) (x,y) * f y) = K.indicator H := by
    funext y
    by_cases hy : y ∈ K
    · simp only [indicator_of_mem hy, indicator_of_mem (show (x,y) ∈ K ×ˢ K from ⟨hx, hy⟩), H]
    · have hy' : (x,y) ∉ K ×ˢ K := fun h => hy h.2
      simp only [indicator_of_notMem hy, indicator_of_notMem hy', zero_mul]
  change Integrable (fun y => (K ×ˢ K).indicator
    (fun p => halfDensityKernelDifference Φ w k p.1 p.2) (x,y) * f y)
  rw [hCut]
  exact (hH.integrableOn_compact hK).integrable_indicator hK.measurableSet

end Burnett.Microlocal.OverlapKernel
