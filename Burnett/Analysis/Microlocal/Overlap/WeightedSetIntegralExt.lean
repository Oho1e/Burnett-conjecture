import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

namespace Burnett.Microlocal.Overlap

open Filter MeasureTheory Set
open scoped NNReal Topology

variable {X Y : Type*} [MeasurableSpace X] [TopologicalSpace Y] [MeasurableSpace Y]
  [HasOuterApproxClosed Y]

private def closedWeight {S : Set Y} (hS : IsClosed S) (n : ℕ) : C(Y, ℂ) :=
  ⟨fun y => ((hS.apprSeq n y : ℝ) : ℂ),
    Complex.continuous_ofReal.comp (NNReal.continuous_coe.comp (hS.apprSeq n).continuous)⟩

private theorem tendsto_closedWeight_preimage [OpensMeasurableSpace Y]
    (μ : Measure X) (φ : X → Y) (hφ : Measurable φ) (f : X → ℂ) (hf : Integrable f μ)
    {S : Set Y} (hS : IsClosed S) :
    Tendsto (fun n => ∫ x, closedWeight hS n (φ x) * f x ∂μ)
      atTop (𝓝 (∫ x in φ ⁻¹' S, f x ∂μ)) := by
  have hBound (n : ℕ) : ∀ᵐ x ∂μ, ‖closedWeight hS n (φ x) * f x‖ ≤ ‖f x‖ := by
    filter_upwards with x
    have ha : ‖closedWeight hS n (φ x)‖ ≤ 1 := by
      rw [closedWeight, ContinuousMap.coe_mk, Complex.norm_real,
        Real.norm_of_nonneg (NNReal.coe_nonneg _)]
      exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hS n (φ x)
    exact (norm_mul _ _).le.trans (mul_le_of_le_one_left (norm_nonneg _) ha)
  have hPoint : ∀ᵐ x ∂μ, Tendsto (fun n => closedWeight hS n (φ x) * f x) atTop
      (𝓝 ((φ ⁻¹' S).indicator f x)) := by
    filter_upwards with x
    have hp := (tendsto_pi_nhds.mp (HasOuterApproxClosed.tendsto_apprSeq hS)) (φ x)
    have hc : Continuous (fun z : ℝ≥0 => ((z : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp NNReal.continuous_coe
    have ht := ((hc.tendsto _).comp hp).mul_const (f x)
    by_cases hx : φ x ∈ S
    · have hx' : x ∈ φ ⁻¹' S := hx
      simpa only [closedWeight, ContinuousMap.coe_mk, Function.comp_apply,
        indicator_of_mem hx, indicator_of_mem hx', NNReal.coe_one, Complex.ofReal_one, one_mul] using ht
    · have hx' : x ∉ φ ⁻¹' S := hx
      simpa only [closedWeight, ContinuousMap.coe_mk, Function.comp_apply,
        indicator_of_notMem hx, indicator_of_notMem hx', NNReal.coe_zero, Complex.ofReal_zero, zero_mul] using ht
  have hT := tendsto_integral_of_dominated_convergence (fun x => ‖f x‖)
    (fun n => ((closedWeight hS n).continuous.measurable.comp hφ).aestronglyMeasurable.mul
      hf.aestronglyMeasurable) hf.norm hBound hPoint
  rw [integral_indicator (hφ hS.measurableSet)] at hT
  exact hT

variable [BorelSpace Y]

/-- Continuous complex tests determine each weighted set integral after a
measurable pullback. Both weights may be complex and merely integrable. -/
theorem setIntegral_preimage_eq_of_continuous_weighted_tests
    (μ : Measure X) (ν : Measure Y) (φ : X → Y) (hφ : Measurable φ)
    (f : X → ℂ) (g : Y → ℂ) (hf : Integrable f μ) (hg : Integrable g ν)
    (h : ∀ a : C(Y, ℂ), (∫ x, a (φ x) * f x ∂μ) = ∫ y, a y * g y ∂ν)
    (S : Set Y) (hS : MeasurableSet S) :
    (∫ x in φ ⁻¹' S, f x ∂μ) = ∫ y in S, g y ∂ν := by
  have hClosed (T : Set Y) (hT : IsClosed T) :
      (∫ x in φ ⁻¹' T, f x ∂μ) = ∫ y in T, g y ∂ν := by
    have hl := tendsto_closedWeight_preimage μ φ hφ f hf hT
    have hr := tendsto_closedWeight_preimage ν id measurable_id g hg hT
    simp_rw [h (closedWeight hT _)] at hl
    exact tendsto_nhds_unique hl hr
  refine MeasurableSpace.induction_on_inter
    (C := fun T _ => (∫ x in φ ⁻¹' T, f x ∂μ) = ∫ y in T, g y ∂ν)
    ((BorelSpace.measurable_eq (α := Y)).trans borel_eq_generateFrom_isClosed)
    isPiSystem_isClosed ?_ (fun T hT => hClosed T hT) ?_ ?_ S hS
  · simp
  · intro T hT heq
    have hAll : (∫ x, f x ∂μ) = ∫ y, g y ∂ν := by
      simpa only [preimage_univ, Measure.restrict_univ] using hClosed univ isClosed_univ
    rw [preimage_compl, setIntegral_compl (hφ hT) hf, setIntegral_compl hT hg, hAll, heq]
  · intro T hDisjoint hT heq
    have hPart : Pairwise (fun i j => Disjoint (φ ⁻¹' T i) (φ ⁻¹' T j)) :=
      fun i j hij => (hDisjoint hij).preimage φ
    rw [preimage_iUnion, integral_iUnion (fun n => hφ (hT n)) hPart hf.integrableOn,
      integral_iUnion hT hDisjoint hg.integrableOn]
    exact tsum_congr heq

end Burnett.Microlocal.Overlap
