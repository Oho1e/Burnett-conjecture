import Burnett.Analysis.Microlocal.Overlap.FrozenShellSymbol
import Burnett.Geometry.ActualChartSecondJet
import Burnett.Geometry.Cotangent.ChartTransition

/-!
# Smooth frequency change for the frozen chart derivative

On the actual overlap the inverse adjoint is the adjoint of the
derivative of the reverse chart evaluated at the image point.
-/

set_option autoImplicit false

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open Set Matrix Burnett.Analysis.CapFourier Burnett.RicciSymbol
open Burnett.Geometry.ActualChartSecondJet (contDiffOn_chartTransition_infty)
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.UnitNullCompactness (cotangentTransitionMatrix)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient
open scoped ContDiff Manifold Matrix

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The moving frequency map using the reverse chart derivative. -/
def chartTransitionFrequency (c d : M) (x : E) : E →L[ℝ] E :=
  (fderiv ℝ (chartTransition d c) (chartTransition c d x)).adjoint

theorem chartTransitionFrequency_eq_frozen (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) (ξ : E) :
    chartTransitionFrequency c d x ξ = frozenChartFrequency c d hx ξ := by
  let A := frozenChartDerivative c d hx
  let J := fderiv ℝ (overlapTransition c d) x
  let K := fderiv ℝ (chartTransition d c) (chartTransition c d x)
  have hA : A.toContinuousLinearMap = J :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero _ _
  have hComp : K.comp J = ContinuousLinearMap.id ℝ E := by
    change K.comp (fderiv ℝ (overlapTransition c d) x) = _
    rw [overlapTransition_fderiv c d hx]
    exact chartTransition_fderiv_leftInverse c d hx
  have hDual : J.adjoint.comp K.adjoint = ContinuousLinearMap.id ℝ E := by
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id] using
      congrArg (fun L : E →L[ℝ] E => L.adjoint) hComp
  apply (physicalDualEquiv A).injective
  change (physicalDualEquiv A) (K.adjoint ξ) = (physicalDualEquiv A) ((physicalDualEquiv A).symm ξ)
  rw [ContinuousLinearEquiv.apply_symm_apply, physicalDualEquiv_apply, hA]
  exact congrArg (fun L : E →L[ℝ] E => L ξ) hDual

private theorem derivativeMatrix_adjoint_real (L : E →L[ℝ] E) :
    derivativeMatrix L.adjoint = (derivativeMatrix L)ᵀ := by
  let b := EuclideanSpace.basisFun Index ℝ
  have h := LinearMap.toMatrix_adjoint b b L.toLinearMap
  change derivativeMatrix L.adjoint = (derivativeMatrix L)ᴴ at h
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h

/-- The frozen Fourier frequency has the components of the actual
covector in the other preferred chart. -/
theorem frozenChartFrequency_cotangentCoords (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) (ξ : E) :
    (fun i : Index => frozenChartFrequency c d hx ξ i) =
      cotangentTransitionMatrix c d ((chartAt CoordinateSpace c).symm x) *ᵥ
        (fun i : Index => ξ i) := by
  let L := chartTransitionFrequency c d x
  have h := LinearMap.toMatrix_mulVec_repr coordinateBasis coordinateBasis L.toLinearMap ξ
  change derivativeMatrix L *ᵥ (fun i : Index => ξ i) = (fun i : Index => L ξ i) at h
  simp_rw [← chartTransitionFrequency_eq_frozen c d hx]
  change (fun i : Index => L ξ i) = _
  rw [← h]
  unfold L chartTransitionFrequency cotangentTransitionMatrix
  rw [derivativeMatrix_adjoint_real]
  rfl

private def realAdjointCLM : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) :=
  (ContinuousLinearMap.adjoint (𝕜 := ℝ)).toContinuousLinearEquiv.toContinuousLinearMap

theorem contDiffOn_chartTransitionFrequency (c d : M) :
    ContDiffOn ℝ ∞ (chartTransitionFrequency c d) (chartTransition c d).source := by
  let e := chartTransition c d
  let f := chartTransition d c
  have hs : e.symm = f := by
    simp only [e, f, chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
      OpenPartialHomeomorph.symm_symm]
  have hm : MapsTo e e.source f.source := by
    rw [← hs]
    exact e.mapsTo
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ f) f.source :=
    (contDiffOn_chartTransition_infty d c).fderiv_of_isOpen f.open_source (by simp)
  exact realAdjointCLM.contDiff.comp_contDiffOn
    (hD.comp (contDiffOn_chartTransition_infty c d) hm)

/-- On a fixed compact overlap window, both frequency maps have bounded
operator norm, uniformly over all input covectors. -/
theorem exists_frozenChartFrequency_norm_bounds (c d : M) (K : Set E)
    (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source) :
    ∃ l u : ℝ, 0 < l ∧ 0 < u ∧ ∀ x (hx : x ∈ K) (ξ : E),
      l * ‖ξ‖ ≤ ‖frozenChartFrequency c d (hKU hx) ξ‖ ∧
        ‖frozenChartFrequency c d (hKU hx) ξ‖ ≤ u * ‖ξ‖ := by
  let D (x : E) : E →L[ℝ] E := (fderiv ℝ (chartTransition c d) x).adjoint
  have hDiff : ContDiffOn ℝ 0 (fderiv ℝ (chartTransition c d)) (chartTransition c d).source :=
    (contDiffOn_chartTransition_infty c d).fderiv_of_isOpen (chartTransition c d).open_source (by simp)
  have hD : ContinuousOn D (chartTransition c d).source :=
    realAdjointCLM.continuous.comp_continuousOn hDiff.continuousOn
  obtain ⟨L, hL, hDL⟩ := (hK.image_of_continuousOn (hD.mono hKU)).isBounded.exists_pos_norm_le
  obtain ⟨U, hU, hFU⟩ := (hK.image_of_continuousOn
    ((contDiffOn_chartTransitionFrequency c d).continuousOn.mono hKU)).isBounded.exists_pos_norm_le
  refine ⟨L⁻¹, U, inv_pos.mpr hL, hU, fun x hx ξ => ⟨?_, ?_⟩⟩
  · let η := frozenChartFrequency c d (hKU hx) ξ
    have hInv : D x η = ξ := by
      unfold D
      rw [← overlapTransition_fderiv c d (hKU hx)]
      exact frozenChartFrequency_inverse_adjoint c d (hKU hx) ξ
    have hB : ‖ξ‖ ≤ L * ‖η‖ := by
      rw [← hInv]
      exact ((D x).le_opNorm η).trans
        (mul_le_mul_of_nonneg_right (hDL _ (mem_image_of_mem _ hx)) (norm_nonneg _))
    rwa [inv_mul_eq_div, div_le_iff₀ hL, mul_comm]
  · rw [← chartTransitionFrequency_eq_frozen c d (hKU hx)]
    exact ((chartTransitionFrequency c d x).le_opNorm ξ).trans
      (mul_le_mul_of_nonneg_right (hFU _ (mem_image_of_mem _ hx)) (norm_nonneg _))

end Burnett.Microlocal.OverlapKernel
