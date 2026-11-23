import Burnett.Analysis.Microlocal.Overlap.HalfDensityKernelTransport
import Burnett.Geometry.MetricJetNaturality

set_option autoImplicit false
set_option maxHeartbeats 1200000

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open Set Burnett.RicciSymbol
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.MetricJetNaturality (derivativeMatrix_apply)
open Burnett.Geometry.SmoothMetricConnection (contDiffOn_det)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The genuine Jacobian half-weight is smooth on the overlap, by smoothness
and nonsingularity of the actual chart derivative. -/
theorem overlapJacobianWeight_smoothOn_source (c d : M) :
    ContDiffOn ℝ ∞ (overlapJacobianWeight c d) (chartTransition c d).source := by
  let U := (chartTransition c d).source
  let Φ := overlapTransition c d
  let A (x : E) := derivativeMatrix (fderiv ℝ Φ x)
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ Φ) U :=
    (overlapTransition_contDiffOn c d).fderiv_of_isOpen (chartTransition c d).open_source (by simp)
  have hA (a b : Index) : ContDiffOn ℝ ∞ (fun x => A x a b) U := by
    simpa only [A, derivativeMatrix_apply] using
      (EuclideanSpace.proj (𝕜 := ℝ) a).contDiff.comp_contDiffOn
        (hD.clm_apply (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : E => coordinateBasis b) U))
  have hDet : ContDiffOn ℝ ∞ (fun x => (fderiv ℝ Φ x).det) U := by
    simpa only [A, det_derivativeMatrix] using contDiffOn_det A U hA
  have hNonzero (x : E) (hx : x ∈ U) : (fderiv ℝ Φ x).det ≠ 0 :=
    overlapTransition_fderiv_det_ne_zero c d hx
  have hAbs := hDet.abs hNonzero
  exact hAbs.sqrt (fun x hx => (abs_pos.mpr (hNonzero x hx)).ne')

/-- A source field supported in the compact window is transported smoothly
across its target support boundary and has the indicated compact support. -/
theorem transportedHalfDensity_smooth_compact_support
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (f : SchwartzMap E ℂ) (hfS : tsupport (f : E → ℂ) ⊆ K) :
    ContDiff ℝ ∞ (transportedHalfDensity c d K f) ∧
      HasCompactSupport (transportedHalfDensity c d K f) ∧
      tsupport (transportedHalfDensity c d K f) ⊆ chartTransition c d '' K := by
  let e := chartTransition c d
  let U := e '' K
  let F := transportedHalfDensity c d K f
  let g (z : E) := overlapJacobianWeight d c z • f (overlapTransition d c z)
  have hU : IsCompact U := hK.image_of_continuousOn (e.continuousOn.mono hKU)
  have hUT : U ⊆ e.target := image_subset_iff.mpr (e.mapsTo.mono_left hKU)
  have hF : tsupport F ⊆ U := by
    apply closure_minimal _ hU.isClosed
    intro z hz
    by_contra hn
    exact hz (Set.indicator_of_notMem hn g)
  have hsymm : e.symm = chartTransition d c := by
    simp only [e, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hV : e.target = (chartTransition d c).source := by
    change e.symm.source = _
    rw [hsymm]
  have hLocal : ContDiffOn ℝ ∞ F e.target := by
    have hg : ContDiffOn ℝ ∞ g (chartTransition d c).source :=
      (overlapJacobianWeight_smoothOn_source d c).smul
        (f.smooth'.comp_contDiffOn (overlapTransition_contDiffOn d c))
    rw [hV]
    refine hg.congr ?_
    intro z hz
    by_cases hzu : z ∈ U
    · exact Set.indicator_of_mem hzu g
    · have hzt : z ∈ e.target := hV.symm ▸ hz
      have hInv : overlapTransition d c z = e.symm z := overlapTransition_eq d c hz |>.trans
        (congrArg (fun a : OpenPartialHomeomorph E E => a z) hsymm.symm)
      have hOutside : e.symm z ∉ K := fun hzK => hzu ⟨e.symm z, hzK, e.right_inv hzt⟩
      have hZero : f (e.symm z) = 0 := image_eq_zero_of_notMem_tsupport
        (fun h : e.symm z ∈ tsupport (f : E → ℂ) => hOutside (hfS h))
      change U.indicator g z = _
      rw [Set.indicator_of_notMem hzu]
      simp only [g, hInv, hZero, smul_zero]
  have hSmooth : ContDiff ℝ ∞ F := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ e.target
    · exact hLocal.contDiffAt (e.open_target.mem_nhds hz)
    · have hOff : z ∉ tsupport F := fun h => hz (hUT (hF h))
      apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : E => (0 : ℂ)) z).congr_of_eventuallyEq
      exact notMem_tsupport_iff_eventuallyEq.mp hOff
  exact ⟨hSmooth, hU.of_isClosed_subset isClosed_closure hF, hF⟩

/-- A Schwartz witness for exactly the zero-extended transported field. -/
def transportedHalfDensitySchwartz
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (f : SchwartzMap E ℂ) (hfS : tsupport (f : E → ℂ) ⊆ K) : SchwartzMap E ℂ :=
  let h := transportedHalfDensity_smooth_compact_support c d K hK hKU f hfS
  h.2.1.toSchwartzMap h.1

@[simp]
theorem coe_transportedHalfDensitySchwartz
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (f : SchwartzMap E ℂ) (hfS : tsupport (f : E → ℂ) ⊆ K) :
    (transportedHalfDensitySchwartz c d K hK hKU f hfS : E → ℂ) =
      transportedHalfDensity c d K f := rfl

end Burnett.Microlocal.OverlapKernel
