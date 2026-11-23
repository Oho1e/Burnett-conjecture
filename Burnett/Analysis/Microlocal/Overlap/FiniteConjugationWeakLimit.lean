import Burnett.Analysis.Microlocal.Overlap.ActualDyadicKernelWeakLimit
import Burnett.Analysis.Microlocal.Overlap.FiniteAngularConjugation

set_option autoImplicit false
set_option maxHeartbeats 1800000

noncomputable section

namespace Burnett.Microlocal.Overlap

open MeasureTheory Set Filter Burnett.Fourier Burnett.Geometry
open Burnett.Geometry.ConnectionDifference Burnett.Geometry.ManifoldBilinear
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Geometry.ChartVolume (chartTransition)
open Burnett.Microlocal.AngularCommutator (DegreeZero)
open Burnett.Microlocal.AngularDyadicKernel (E partialAngularSymbol)
open Burnett.Microlocal.OverlapGradient Burnett.Microlocal.OverlapKernel
open scoped BigOperators ContDiff FourierTransform Manifold InnerProduct Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The difference of the two explicit finite Fourier actions, restricted to
the compact overlap window. -/
def localizedPartialAngularDifference (c d : M) (K : Set E)
    (hKU : K ⊆ (chartTransition c d).source) (m : BoundedSymbol E) (N : ℕ)
    (f : E → ℂ) (x : E) : ℂ := by
  classical
  exact if hx : x ∈ K then
    overlapJacobianWeight c d x •
        (𝓕⁻ (fun ξ => partialAngularSymbol m N ξ * (𝓕 (transportedHalfDensity c d K f)) ξ))
          (overlapTransition c d x) -
      (𝓕⁻ (fun ξ => partialAngularSymbol m N (frozenChartFrequency c d (hKU hx) ξ) *
        (𝓕 (K.indicator f)) ξ)) x
    else 0

/-- For each input, the finite Fourier differences have a strong L² limit
as the number of shells grows. These limits vanish on a bounded weakly null
sequence of inputs. -/
theorem exists_localizedPartialAngularDifference_limit
    (B : Field (M := M)) (hB : IsSmooth B) (hn : IsNondegenerate B)
    (c d : M) (K : Set E) (hK : IsCompact K)
    (hKU : K ⊆ (chartTransition c d).source) (hConv : Convex ℝ K)
    (m : BoundedSymbol E) (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (hd : DegreeZero (m : E → ℂ)) (f : ℕ → SchwartzMap E ℂ)
    (C : ℝ) (hC : ∀ n, ‖(f n).toLp 2 volume‖ ≤ C)
    (hw : ∀ w : ComplexL2 E, Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ F : ℕ → ℕ → ComplexL2 E, ∃ R : ℕ → ComplexL2 E,
      (∀ n N, F n N =ᵐ[volume] localizedPartialAngularDifference c d K hKU m N (f n)) ∧
      (∀ n, Tendsto (F n) atTop (𝓝 (R n))) ∧ Tendsto R atTop (𝓝 0) := by
  let J (j n : ℕ) (x : E) :=
    ∫ y, localizedOverlapShellDifference c d K m hm j x y * f n y
  obtain ⟨U, hU, hSummable, hLimit⟩ := exists_actualOverlapShell_actions_tendsto_zero
    B hB hn c d K hK hKU hConv m hm (fun n => (f n : E → ℂ))
    (fun n => (f n).continuous.measurable) (fun n => (f n).integrable)
    (fun n => (f n).memLp 2 volume) C hC hw
  let F (n N : ℕ) := ∑ j ∈ Finset.range N, U j n
  let R (n : ℕ) := ∑' j, U j n
  have hAE (n N : ℕ) : (F n N : E → ℂ) =ᵐ[volume] fun x => ∑ j ∈ Finset.range N, J j n x := by
    induction N with
    | zero => simpa only [F, Finset.sum_range_zero] using
        (Lp.coeFn_zero ℂ 2 (volume : Measure E))
    | succ N ih =>
        simp only [F, Finset.sum_range_succ]
        filter_upwards [Lp.coeFn_add (F n N) (U N n), ih, hU N n] with x hx hxSum hxTerm
        simpa only [Pi.add_apply, hxSum, hxTerm, J] using hx
  refine ⟨F, R, ?_, fun n => (hSummable n).of_norm.hasSum.tendsto_sum_nat, hLimit⟩
  intro n N
  filter_upwards [hAE n N] with x hX
  rw [hX]
  by_cases hx : x ∈ K
  · simp only [localizedPartialAngularDifference, dif_pos hx]
    exact (overlap_partialAngularFourier_difference_sum_actions c d K hK hKU hx m hm hd N
      (f n) (f n).continuous).symm
  · have jZero (j : ℕ) : J j n x = 0 := by
      have hxy (y : E) : (x,y) ∉ K ×ˢ K := fun h => hx h.1
      simp only [J, localizedOverlapShellDifference, indicator_of_notMem (hxy _), zero_mul, integral_zero]
    simp only [localizedPartialAngularDifference, dif_neg hx, jZero, Finset.sum_const_zero]

end Burnett.Microlocal.Overlap
