import Burnett.Analysis.Microlocal.Overlap.BaseFourierAngularRegularity
import Burnett.Analysis.Microlocal.Overlap.CompactFrequencyLeftAction
import Burnett.Analysis.Microlocal.Overlap.MovingChartInfrared

set_option autoImplicit false
set_option maxHeartbeats 4500000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter Function MeasureTheory Metric Set Burnett.Fourier
open Burnett.Analysis.FirstOrderDyadic (firstOrderAction)
open Burnett.Geometry.ChartVolume Burnett.Geometry.ConnectionDifference
open Burnett.Geometry.ManifoldMetric (Model)
open Burnett.Microlocal.AngularDyadicKernel
open Burnett.Microlocal.OverlapKernel
open scoped ContDiff FourierTransform InnerProduct Manifold Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]

/-- The low frequency portion of the moving homogeneous symbol. -/
def movingChartLowSymbol (c d : M) (a m : E → ℂ) (x ξ : E) : ℂ :=
  (↑(radialCore (chartTransitionFrequency c d x ξ)) : ℂ) * movingChartAngularSymbol c d a m (x,ξ)

omit [IsManifold Model ∞ M] in
private theorem movingChartLowSymbol_eq (c d : M) (a m : E → ℂ) (x ξ : E) :
    movingChartLowSymbol c d a m x ξ =
      (↑(radialCore ξ) : ℂ) * movingChartAngularSymbol c d a m (x,ξ) -
        movingChartInfraredRemainder c d a m (x,ξ) := by
  unfold movingChartLowSymbol movingChartInfraredRemainder
  push_cast
  ring

theorem measurable_movingChartLowSymbol (c d : M) (a m : E → ℂ)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ (chartTransition c d).source)
    (hSupport : tsupport a ⊆ S) (ha : ContDiff ℝ ∞ a)
    (hm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set E)) :
    Measurable (uncurry (movingChartLowSymbol c d a m)) := by
  let p (x ξ : E) := movingChartAngularSymbol c d a m (x,ξ)
  have hJoint : ContDiffOn ℝ ∞ (uncurry p) (univ ×ˢ ({0}ᶜ : Set E)) :=
    contDiffOn_movingChartAngularSymbol c d a m ha (hSupport.trans hSU) hm
  have hZero : ContDiff ℝ ∞ (fun x => p x 0) := by
    simp only [p, movingChartAngularSymbol, map_zero]
    exact ha.mul contDiff_const
  have hp : Measurable (uncurry p) :=
    measurable_baseAngularSymbol
      (fun ξ => (contDiff_baseAngularSection p hJoint hZero ξ).continuous)
      (fun x => hJoint.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn
        (fun _ hξ => ⟨mem_univ x, hξ⟩))
  have hrad : Measurable (fun q : E × E => (↑(radialCore q.2) : ℂ)) :=
    (Complex.continuous_ofReal.comp (radialCore_contDiff.continuous.comp continuous_snd)).measurable
  have hrem : Measurable (movingChartInfraredRemainder c d a m) :=
    (contDiff_movingChartInfraredRemainder c d a m S hS hSU hSupport ha hm).continuous.measurable
  have heq : uncurry (movingChartLowSymbol c d a m) =
      (fun q : E × E => (↑(radialCore q.2) : ℂ) * p q.1 q.2 -
        movingChartInfraredRemainder c d a m q) := by
    funext q
    exact movingChartLowSymbol_eq c d a m q.1 q.2
  rw [heq]
  exact (hrad.mul hp).sub hrem

omit [IsManifold Model ∞ M] in
theorem movingChartLowSymbol_norm_le (c d : M) (a m : BoundedSymbol E) (x ξ : E) :
    ‖movingChartLowSymbol c d a m x ξ‖ ≤ a.bound * m.bound := by
  rw [movingChartLowSymbol, norm_mul, Complex.norm_real, Real.norm_of_nonneg (radialCore_nonneg _)]
  exact ((mul_le_mul_of_nonneg_right (radialCore_le_one _) (norm_nonneg _)).trans_eq
    (one_mul _)).trans (movingChartAngularSymbol_norm_le c d a m (x,ξ))

/-- The exact infrared term in the moving coordinate has strong L²
limit zero on the original weakly null input. -/
theorem exists_movingChartLowAction_strongZero (c d : M) (a m : BoundedSymbol E)
    (S : Set E) (hS : IsCompact S) (hSU : S ⊆ (chartTransition c d).source)
    (hSupport : tsupport (a : E → ℂ) ⊆ S) (ha : ContDiff ℝ ∞ (a : E → ℂ))
    (hm : ContDiffOn ℝ ∞ (m : E → ℂ) ({0}ᶜ : Set E))
    (f : ℕ → SchwartzMap E ℂ) (B : ℝ) (hB : ∀ n, ‖(f n).toLp 2 volume‖ ≤ B)
    (hw : ∀ w : ComplexL2 E,
      Tendsto (fun n => inner ℂ w ((f n).toLp 2 volume)) atTop (𝓝 0)) :
    ∃ A : ℕ → ComplexL2 E,
      (∀ n, A n =ᵐ[volume] firstOrderAction (movingChartLowSymbol c d a m) (f n)) ∧
      Tendsto A atTop (𝓝 0) := by
  obtain ⟨L, U, hL, _, hLU⟩ := exists_frozenChartFrequency_norm_bounds c d S hS hSU
  have hM := measurable_movingChartLowSymbol c d a m S hS hSU hSupport ha hm
  refine exists_compactFrequency_leftAction_strongZero _ hM S (closedBall 0 (2 / L))
    hS (isCompact_closedBall _ _) ?_ (a.bound * m.bound)
    (mul_nonneg a.bound_nonneg m.bound_nonneg) (movingChartLowSymbol_norm_le c d a m) f B hB hw
  · intro x ξ hxξ
    by_cases hx : x ∈ S
    · have hξ : 2 / L < ‖ξ‖ := by
        simpa only [mem_closedBall, dist_zero_right, not_le] using
          (hxξ.resolve_left (not_not_intro hx))
      have hz : 2 ≤ ‖chartTransitionFrequency c d x ξ‖ := by
        rw [chartTransitionFrequency_eq_frozen c d (hSU hx)]
        have h := (div_le_iff₀ hL).mp hξ.le
        rw [mul_comm] at h
        exact h.trans (hLU x hx ξ).1
      simp only [movingChartLowSymbol, radialCore_eq_zero _ hz, Complex.ofReal_zero, zero_mul]
    · have h0 : a x = 0 :=
        image_eq_zero_of_notMem_tsupport (f := (a : E → ℂ)) (fun h => hx (hSupport h))
      simp only [movingChartLowSymbol, movingChartAngularSymbol, h0, zero_mul, mul_zero]

/-- Pointwise decomposition of the transformed normalized symbol on the overlap. -/
theorem movingChart_normalizedAngular_eq_principal_sub_low (c d : M) (a : E → ℂ)
    (m : BoundedSymbol E) {x : E} (hx : x ∈ (chartTransition c d).source) (ξ : E) :
    a x * normalizedAngularSymbol m (frozenChartFrequency c d hx ξ) =
      movingChartAngularSymbol c d a m (x,ξ) - movingChartLowSymbol c d a m x ξ := by
  rw [movingChartNormalizedSymbol_eq_fixedCore_add c d a m hx ξ, movingChartLowSymbol_eq]
  unfold movingChartFixedCoreSymbol
  push_cast
  ring

end Burnett.Microlocal.Overlap
