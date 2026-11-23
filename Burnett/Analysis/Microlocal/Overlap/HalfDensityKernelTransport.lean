import Burnett.Analysis.Microlocal.Overlap.KernelGeometry
import Burnett.Analysis.PrincipalEnergy.Fourier.DyadicKernel
import Mathlib.MeasureTheory.Function.Jacobian

set_option autoImplicit false
set_option maxHeartbeats 1400000

noncomputable section

namespace Burnett.Microlocal.OverlapKernel

open MeasureTheory Set Burnett.Fourier
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ChartVolume
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel Burnett.Microlocal.OverlapGradient
open scoped ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M]

private theorem chartTransition_symm_eq (c d : M) :
    (chartTransition c d).symm = chartTransition d c := by
  simp only [chartTransition, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm]

private theorem reverse_overlap_source (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) :
    chartTransition c d x ∈ (chartTransition d c).source := by
  rw [← chartTransition_symm_eq c d]
  exact (chartTransition c d).mapsTo hx

theorem overlapTransition_reverse_apply (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) :
    overlapTransition d c (chartTransition c d x) = x := by
  rw [overlapTransition_eq d c (reverse_overlap_source c d hx), ← chartTransition_symm_eq c d]
  exact (chartTransition c d).left_inv hx

theorem overlapJacobianWeight_sq_on_source (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) :
    (overlapJacobianWeight c d x)^2 = |(fderiv ℝ (chartTransition c d) x).det| := by
  rw [overlapJacobianWeight_eq c d hx, Real.sq_sqrt (abs_nonneg _)]

/-- Transport on one source window, with zero extension off its actual
image in the target chart. -/
def transportedHalfDensity (c d : M) (S : Set E) (f : E → ℂ) : E → ℂ :=
  ((chartTransition c d) '' S).indicator
    (fun z => overlapJacobianWeight d c z • f (overlapTransition d c z))

variable [IsManifold Model ∞ M]

private theorem overlapTransition_det_mul_reverse (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) :
    (fderiv ℝ (chartTransition d c) (chartTransition c d x)).det *
      (fderiv ℝ (chartTransition c d) x).det = 1 := by
  let e := chartTransition c d
  have hL : (fderiv ℝ (chartTransition d c) (e x)).toLinearMap.comp (fderiv ℝ e x).toLinearMap =
      LinearMap.id :=
    congrArg ContinuousLinearMap.toLinearMap (chartTransition_fderiv_leftInverse c d hx)
  have hDet := congrArg LinearMap.det hL
  rwa [LinearMap.det_comp, LinearMap.det_id] at hDet

theorem overlapTransition_fderiv_det_ne_zero (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) :
    (fderiv ℝ (overlapTransition c d) x).det ≠ 0 := by
  rw [overlapTransition_fderiv c d hx]
  intro h
  have hd := overlapTransition_det_mul_reverse c d hx
  rw [h, mul_zero] at hd
  exact zero_ne_one hd

theorem overlapJacobianWeight_inverse_mul (c d : M) {x : E}
    (hx : x ∈ (chartTransition c d).source) :
    overlapJacobianWeight c d x * overlapJacobianWeight d c (chartTransition c d x) = 1 := by
  rw [overlapJacobianWeight_eq c d hx, overlapJacobianWeight_eq d c (reverse_overlap_source c d hx),
    mul_comm, ← Real.sqrt_mul (abs_nonneg _), ← abs_mul,
    overlapTransition_det_mul_reverse c d hx, abs_one, Real.sqrt_one]

theorem overlapJacobianWeight_continuousOn (c d : M) :
    ContinuousOn (overlapJacobianWeight c d) (chartTransition c d).source := by
  have hD : ContDiffOn ℝ 0 (fderiv ℝ (overlapTransition c d))
      (chartTransition c d).source :=
    (overlapTransition_contDiffOn c d).fderiv_of_isOpen (chartTransition c d).open_source (by simp)
  unfold overlapJacobianWeight
  exact (Real.continuous_sqrt.comp continuous_abs).comp_continuousOn
    (ContinuousLinearMap.continuous_det.comp_continuousOn hD.continuousOn)

theorem integrable_transportedHalfDensity (c d : M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) {f : E → ℂ} (hf : Continuous f) :
    Integrable (transportedHalfDensity c d K f) := by
  let U := chartTransition c d '' K
  let V := (chartTransition d c).source
  have hU : IsCompact U := hK.image_of_continuousOn ((chartTransition c d).continuousOn.mono hKU)
  have hUV : U ⊆ V := by
    rintro _ ⟨z, hz, rfl⟩
    exact reverse_overlap_source c d (hKU hz)
  have hΦ : ContDiffOn ℝ ∞ (overlapTransition d c) V := overlapTransition_contDiffOn d c
  have hLoc : ContinuousOn
      (fun z => overlapJacobianWeight d c z • f (overlapTransition d c z)) U :=
    ((overlapJacobianWeight_continuousOn d c).mono hUV).smul
      (hf.comp_continuousOn (hΦ.continuousOn.mono hUV))
  exact (hLoc.integrableOn_compact hU).integrable_indicator hU.measurableSet

/-- Change variables in the target convolution pairing. One inverse
half-density cancels one of the two forward factors in the Jacobian. -/
theorem overlap_halfDensityKernel_changeVariables
    (c d : M) (S : Set E) (hS : MeasurableSet S)
    (hSU : S ⊆ (chartTransition c d).source) (k f : E → ℂ) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    w x • (∫ z in chartTransition c d '' S, k (Φ x - z) *
      (overlapJacobianWeight d c z • f (overlapTransition d c z))) =
      ∫ y in S, ((w x * w y) • k (Φ x - Φ y)) * f y := by
  intro Φ w
  let e := chartTransition c d
  let g (z : E) := k (Φ x - z) * (overlapJacobianWeight d c z • f (overlapTransition d c z))
  have hD (y : E) (hy : y ∈ S) : HasFDerivWithinAt e (fderiv ℝ e y) S y :=
    ((((contDiffOn_chartTransition c d).differentiableOn le_rfl) y (hSU hy)).differentiableAt
      (e.open_source.mem_nhds (hSU hy))).hasFDerivAt.hasFDerivWithinAt
  change w x • (∫ z in e '' S, g z) = _
  rw [integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure E) hS hD
    (e.injOn.mono hSU) g, ← integral_smul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hS] with y hy
  have hy' := hSU hy
  have hΦ : Φ y = e y := overlapTransition_eq c d hy'
  rw [hΦ]
  unfold g
  rw [overlapTransition_reverse_apply c d hy', ← overlapJacobianWeight_sq_on_source c d hy']
  have hW : w y * overlapJacobianWeight d c (e y) = 1 :=
    overlapJacobianWeight_inverse_mul c d hy'
  have hWeights : (w x * (w y)^2) * overlapJacobianWeight d c (e y) = w x * w y := by
    calc
      _ = (w x * w y) * (w y * overlapJacobianWeight d c (e y)) := by ring
      _ = _ := by rw [hW, mul_one]
  change w x • ((w y)^2 • (k (Φ x-e y) * (overlapJacobianWeight d c (e y) • f y))) = _
  rw [mul_smul_comm, smul_smul, smul_smul, hWeights, smul_mul_assoc]

/-- With zero extension of the transported input, the full target
convolution pulls back to an integral over the source window. -/
theorem overlap_kernel_conjugation
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (k f : E → ℂ) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    w x • (∫ z, k (Φ x - z) * transportedHalfDensity c d K f z) =
      ∫ y in K, ((w x * w y) • k (Φ x - Φ y)) * f y := by
  intro Φ w
  let U := chartTransition c d '' K
  have hU : MeasurableSet U := (hK.image_of_continuousOn
    ((chartTransition c d).continuousOn.mono hKU)).measurableSet
  let g (z : E) := k (Φ x-z) * (overlapJacobianWeight d c z • f (overlapTransition d c z))
  have he : (fun z => k (Φ x-z) * transportedHalfDensity c d K f z) = U.indicator g := by
    funext z
    by_cases hz : z ∈ U
    · simp only [transportedHalfDensity, U, g, Set.indicator_of_mem hz]
    · simp only [transportedHalfDensity, U, g, Set.indicator_of_notMem hz, mul_zero]
  rw [he, integral_indicator hU]
  exact overlap_halfDensityKernel_changeVariables c d K hK.measurableSet hKU k f x

/-- The full target convolution of the actual inverse Fourier shell,
pulled back to the source. -/
theorem overlap_shellKernel_conjugation
    (c d : M) (K : Set E) (hK : IsCompact K) (hKU : K ⊆ (chartTransition c d).source)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (j : ℕ) (f : E → ℂ) (x : E) :
    let Φ := overlapTransition c d
    let w := overlapJacobianWeight c d
    let k := shellKernel m hm j
    w x • (∫ z, k (Φ x - z) * transportedHalfDensity c d K f z) =
      ∫ y in K, ((w x * w y) • k (Φ x - Φ y)) * f y :=
  overlap_kernel_conjugation c d K hK hKU (shellKernel m hm j) f x

end Burnett.Microlocal.OverlapKernel
