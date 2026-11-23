import Burnett.Analysis.Microlocal.Overlap.DyadicShellInversionLimit

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Filter Burnett.Fourier
open Burnett.Geometry ConnectionDifference ManifoldBilinear
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E normalizedAngularSymbol)
open scoped ContDiff FourierTransform Manifold InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The difference of the actual transported and frozen Fourier actions with
one fixed infrared normalization. -/
def localizedNormalizedAngularDifference (c d : M) (K : Set E)
    (hKU : K ⊆ (chartTransition c d).source) (m : BoundedSymbol E)
    (f : E → ℂ) (x : E) : ℂ := by
  classical
  exact if hx : x ∈ K then
    overlapJacobianWeight c d x •
        (𝓕⁻ (fun ξ => normalizedAngularSymbol m ξ * (𝓕 (transportedHalfDensity c d K f)) ξ))
          (overlapTransition c d x) -
      (𝓕⁻ (fun ξ => normalizedAngularSymbol m (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x
    else 0

theorem tendsto_localizedPartialAngularDifference
    (c d : M) (K : Set E) (hKU : K ⊆ (chartTransition c d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : E → ℂ) (hf : Integrable (𝓕 (K.indicator f)))
    (hTransport : Integrable (𝓕 (transportedHalfDensity c d K f))) (x : E) :
    Tendsto (fun N => localizedPartialAngularDifference c d K hKU m N f x) atTop
      (𝓝 (localizedNormalizedAngularDifference c d K hKU m f x)) := by
  by_cases hx : x ∈ K
  · simp only [localizedPartialAngularDifference, localizedNormalizedAngularDifference, dif_pos hx]
    have hTarget := tendsto_inverseFourier_partialAngular_comp m hm id measurable_id
      (𝓕 (transportedHalfDensity c d K f)) hTransport (overlapTransition c d x)
    have hFrozen := tendsto_inverseFourier_partialAngular_comp m hm
      (frozenChartFrequency c d (hKU hx))
      (frozenChartFrequency c d (hKU hx)).continuous.measurable (𝓕 (K.indicator f)) hf x
    exact (hTarget.const_smul (overlapJacobianWeight c d x)).sub hFrozen
  · simp only [localizedPartialAngularDifference, localizedNormalizedAngularDifference, dif_neg hx]
    exact tendsto_const_nhds

/-- Removing the outer cutoff gives the actual Fourier difference in L².
The identified differences vanish strongly on bounded weakly null inputs. -/
theorem exists_localizedNormalizedAngularDifference_strongZero
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c d : M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : ℕ → SchwartzMap E ℂ)
    (hf : ∀ n, Integrable (𝓕 (K.indicator (f n : E → ℂ))))
    (hTransport : ∀ n, Integrable (𝓕 (transportedHalfDensity c d K (f n))))
    (C : ℝ) (hC : ∀ n, ‖(f n).toLp 2 volume‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ R : ℕ → ComplexL2 E,
      (∀ n, R n =ᵐ[volume] localizedNormalizedAngularDifference c d K hKU m (f n)) ∧
      Tendsto R atTop (𝓝 0) := by
  obtain ⟨F, R, hEq, hOuter, hZero⟩ := exists_localizedPartialAngularDifference_limit
    B hB hn c d K hK hKU hConv m hm hd f C hC hw
  refine ⟨R, fun n => ?_, hZero⟩
  exact ae_eq_of_tendsto_L2_and_pointwise (F n) (R n)
    (fun N => localizedPartialAngularDifference c d K hKU m N (f n)) _ (hEq n) (hOuter n)
    (tendsto_localizedPartialAngularDifference c d K hKU m hm (f n) (hf n) (hTransport n))

end Burnett.Microlocal.Overlap
