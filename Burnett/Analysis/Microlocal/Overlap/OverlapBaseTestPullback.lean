import Burnett.Analysis.Microlocal.Overlap.Localization
import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Set Burnett.Fourier
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ActualChartSecondJet (contDiffOn_chartTransition_infty)
open Burnett.Microlocal.AngularDyadicKernel (E)
open scoped ContDiff Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- A smooth target test supported in the image of a compact source window
pulls back to a smooth bounded test supported in that same source window. -/
theorem exists_overlapBaseTest_pullback (c d : M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (chartTransition c d).source) (b : BoundedSymbol E)
    (hb : ContDiff ℝ ∞ (b : E → ℂ)) (hSupport : tsupport (b : E → ℂ) ⊆ chartTransition c d '' S) :
    ∃ a : BoundedSymbol E, ContDiff ℝ ∞ (a : E → ℂ) ∧ tsupport (a : E → ℂ) ⊆ S ∧
      a.bound = b.bound ∧ ∀ x ∈ (chartTransition c d).source, a x = b (chartTransition c d x) := by
  let e := chartTransition c d
  let f : E → ℂ := e.source.indicator ((b : E → ℂ) ∘ e)
  have hSup : tsupport f ⊆ S := by
    apply closure_minimal _ hS.isClosed
    intro x hx
    have hne : f x ≠ 0 := hx
    have hxs : x ∈ e.source := by
      by_contra h
      exact hne (indicator_of_notMem h _)
    have hbx : b (e x) ≠ 0 := by
      simpa only [f, indicator_of_mem hxs, Function.comp_apply] using hne
    obtain ⟨y, hy, hEq⟩ := hSupport (subset_tsupport (b : E → ℂ) hbx)
    exact (e.injOn (hSU hy) hxs hEq) ▸ hy
  have hAt : ∀ x ∈ e.source, f x = b (e x) := fun _ hx => indicator_of_mem hx _
  have hLoc : ContDiffOn ℝ ∞ f e.source :=
    (hb.comp_contDiffOn (contDiffOn_chartTransition_infty c d)).congr hAt
  have hSmooth : ContDiff ℝ ∞ f := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : x ∈ e.source
    · exact hLoc.contDiffAt (e.open_source.mem_nhds hx)
    · have hn : x ∉ tsupport f := fun h => hx (hSU (hSup h))
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) x).congr_of_eventuallyEq
      exact notMem_tsupport_iff_eventuallyEq.mp hn
  let a : BoundedSymbol E := {
    toFun := f
    measurable := hSmooth.continuous.measurable.aestronglyMeasurable
    bound := b.bound
    bound_nonneg := b.bound_nonneg
    norm_le := fun x => by
      by_cases hx : x ∈ e.source
      · rw [hAt x hx]
        exact b.norm_le (e x)
      · simp only [f, indicator_of_notMem hx, norm_zero]
        exact b.bound_nonneg
  }
  exact ⟨a, hSmooth, hSup, rfl, hAt⟩

end Burnett.Microlocal.Overlap
