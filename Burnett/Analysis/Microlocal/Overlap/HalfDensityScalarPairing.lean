import Burnett.Analysis.Microlocal.Overlap.HalfDensityKernelTransport

set_option autoImplicit false
set_option maxHeartbeats 3000000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set
open Burnett.Geometry.ChartVolume (chartTransition contDiffOn_chartTransition)
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel (E)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open scoped ComplexConjugate ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The half-density pullback moves the target scalar pairing onto the
same source overlap window. The zero extensions use the actual image. -/
theorem integral_transportHalfDensity_pairing (c d : M) (S : Set E) (hS : IsCompact S)
    (hSU : S ⊆ (chartTransition c d).source) (f a v : E → ℂ) :
    (∫ y, conj (transportedHalfDensity c d S f y) * (a y * v y)) =
      ∫ x, conj (f x) * (a (overlapTransition c d x) *
        S.indicator (fun z => overlapJacobianWeight c d z • v (overlapTransition c d z)) x) := by
  let e := chartTransition c d
  let U := e '' S
  let F (y : E) := conj (overlapJacobianWeight d c y • f (overlapTransition d c y)) * (a y * v y)
  let G (x : E) := conj (f x) * (a (overlapTransition c d x) *
    (overlapJacobianWeight c d x • v (overlapTransition c d x)))
  have hU : IsCompact U := hS.image_of_continuousOn (e.continuousOn.mono hSU)
  have hL : (fun y => conj (transportedHalfDensity c d S f y) * (a y * v y)) = U.indicator F := by
    funext y
    by_cases hy : y ∈ U
    · simp only [transportedHalfDensity, U, e, F, indicator_of_mem hy]
    · simp only [transportedHalfDensity, U, e, indicator_of_notMem hy, map_zero, zero_mul]
  have hR : (fun x => conj (f x) * (a (overlapTransition c d x) *
      S.indicator (fun z => overlapJacobianWeight c d z • v (overlapTransition c d z)) x)) =
      S.indicator G := by
    funext x
    by_cases hx : x ∈ S
    · simp only [G, indicator_of_mem hx]
    · simp only [indicator_of_notMem hx, mul_zero]
  have hD (x : E) (hx : x ∈ S) : HasFDerivWithinAt e (fderiv ℝ e x) S x :=
    ((((contDiffOn_chartTransition c d).differentiableOn le_rfl) x (hSU hx)).differentiableAt
      (e.open_source.mem_nhds (hSU hx))).hasFDerivAt.hasFDerivWithinAt
  rw [hL, hR, integral_indicator hU.measurableSet, integral_indicator hS.measurableSet,
    integral_image_eq_integral_abs_det_fderiv_smul (volume : Measure E) hS.measurableSet hD
      (e.injOn.mono hSU) F]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem (μ := volume) hS.measurableSet] with x hx
  let W := overlapJacobianWeight c d x
  let V := overlapJacobianWeight d c (e x)
  have hW : W * V = 1 := overlapJacobianWeight_inverse_mul c d (hSU hx)
  have hWc : (W : ℂ) * (V : ℂ) = 1 := by exact_mod_cast hW
  change |(fderiv ℝ e x).det| • F (e x) = G x
  rw [← overlapJacobianWeight_sq_on_source c d (hSU hx)]
  unfold F G
  rw [overlapTransition_reverse_apply c d (hSU hx), overlapTransition_eq c d (hSU hx)]
  simp only [Complex.real_smul, map_mul, Complex.conj_ofReal, Complex.ofReal_pow]
  change (W : ℂ)^2 * ((V : ℂ) * conj (f x) * (a (e x) * v (e x))) =
    conj (f x) * (a (e x) * ((W : ℂ) * v (e x)))
  calc
    _ = (W : ℂ) * ((W : ℂ) * (V : ℂ)) * (conj (f x) * (a (e x) * v (e x))) := by ring
    _ = _ := by rw [hWc, mul_one]; ring

end Burnett.Microlocal.Overlap
