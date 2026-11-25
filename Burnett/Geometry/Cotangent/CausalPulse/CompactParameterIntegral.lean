import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.Order.Compact

set_option autoImplicit false
set_option maxHeartbeats 5600000

noncomputable section

namespace Burnett.GeometricAnalysis

open Set Filter MeasureTheory
open scoped ContDiff Topology

universe u

variable {P F : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

private def parameterDerivative (f : P × ℝ → F) (z : P × ℝ) : P →L[ℝ] F :=
  (fderiv ℝ f z).comp ((ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] ℝ))

omit [FiniteDimensional ℝ P] [FiniteDimensional ℝ F] in
private theorem contDiffOn_parameterDerivative {f : P × ℝ → F} {U : Set P} {V : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) :
    ContDiffOn ℝ ∞ (parameterDerivative f) (U ×ˢ V) :=
  (hf.fderiv_of_isOpen (hU.prod hV) (by simp)).clm_comp contDiffOn_const

private theorem hasFDerivAt_compact_parameter_integral {f : P × ℝ → F} {U : Set P} {V K : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) {x₀ : P} (hx₀ : x₀ ∈ U) :
    HasFDerivAt (fun x => ∫ t in K, f (x, t)) (∫ t in K, parameterDerivative f (x₀, t)) x₀ := by
  let μ := (volume : Measure ℝ).restrict K
  letI : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr (hK.measure_lt_top (μ := volume)).ne
  have hDerivOn := contDiffOn_parameterDerivative hU hV hf
  obtain ⟨r, hr, hBall⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hx₀)
  let ε := r / 2
  have hε : 0 < ε := half_pos hr
  let B := Metric.closedBall x₀ ε
  have hBU : B ⊆ U := (Metric.closedBall_subset_ball (half_lt_self hr)).trans hBall
  have hSup : ContinuousOn (fun z => ‖parameterDerivative f z‖) (B ×ˢ K) :=
    hDerivOn.continuousOn.norm.mono (prod_mono hBU hKV)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall x₀ ε).prod hK).bddAbove_image hSup
  have hSlice (x : P) (hx : x ∈ U) : ContinuousOn (fun t : ℝ => f (x, t)) K :=
    hf.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hx, hKV ht⟩)
  have hSliceD : ContinuousOn (fun t : ℝ => parameterDerivative f (x₀, t)) K :=
    hDerivOn.continuousOn.comp (continuous_const.prodMk continuous_id).continuousOn (fun _ ht => ⟨hx₀, hKV ht⟩)
  have hMeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (fun t : ℝ => f (x, t)) μ := by
    have hNear : ∀ᶠ x in 𝓝 x₀, x ∈ U := hU.mem_nhds hx₀
    exact hNear.mono fun x hx => (hSlice x hx).aestronglyMeasurable hK.measurableSet
  have hIntegrable : Integrable (fun t : ℝ => f (x₀, t)) μ := (hSlice x₀ hx₀).integrableOn_compact hK
  have hDMeas : AEStronglyMeasurable (fun t : ℝ => parameterDerivative f (x₀, t)) μ :=
    hSliceD.aestronglyMeasurable hK.measurableSet
  have hKae : ∀ᵐ t ∂μ, t ∈ K := ae_restrict_mem hK.measurableSet
  have hBound : ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ ε, ‖parameterDerivative f (x, t)‖ ≤ C :=
    hKae.mono fun t ht x hx => hC (mem_image_of_mem _ ⟨Metric.ball_subset_closedBall hx, ht⟩)
  have hDiff : ∀ᵐ t ∂μ, ∀ x ∈ Metric.ball x₀ ε, HasFDerivAt (fun p => f (p, t))
      (parameterDerivative f (x, t)) x := by
    filter_upwards [hKae] with t ht x hx
    have hUV : (x, t) ∈ U ×ˢ V := ⟨hBU (Metric.ball_subset_closedBall hx), hKV ht⟩
    have hAt := (hf.contDiffAt ((hU.prod hV).mem_nhds hUV)).differentiableAt (by simp)
    exact hAt.hasFDerivAt.comp x ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F := fun x t => f (x, t)) hε hMeas hIntegrable
    hDMeas hBound (integrable_const C) hDiff

private theorem contDiffOn_nat_compact_parameter_integral (n : ℕ) {f : P × ℝ → F} {U : Set P} {V K : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) : ContDiffOn ℝ n (fun x => ∫ t in K, f (x, t)) U := by
  induction n generalizing F with
  | zero =>
      apply contDiffOn_zero.mpr
      intro x hx
      exact (hasFDerivAt_compact_parameter_integral hU hV hK hKV hf hx).continuousAt.continuousWithinAt
  | succ n ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderiv_of_isOpen hU]
      refine ⟨fun x hx => (hasFDerivAt_compact_parameter_integral hU hV hK hKV hf hx).differentiableAt.differentiableWithinAt,
        by simp, ?_⟩
      have hD := ih (contDiffOn_parameterDerivative hU hV hf)
      exact hD.congr (fun x hx => (hasFDerivAt_compact_parameter_integral hU hV hK hKV hf hx).fderiv)

/-- Integrating a jointly smooth function over a fixed compact parameter
set preserves smoothness in the other variable. -/
theorem contDiffOn_compact_parameter_integral {f : P × ℝ → F} {U : Set P} {V K : Set ℝ}
    (hU : IsOpen U) (hV : IsOpen V) (hK : IsCompact K) (hKV : K ⊆ V)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ V)) : ContDiffOn ℝ ∞ (fun x => ∫ t in K, f (x, t)) U :=
  contDiffOn_infty.mpr fun n => contDiffOn_nat_compact_parameter_integral n hU hV hK hKV hf

end Burnett.GeometricAnalysis
