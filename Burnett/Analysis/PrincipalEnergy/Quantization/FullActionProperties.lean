import Burnett.Analysis.PrincipalEnergy.Quantization.FullApproximateConstant
import Burnett.Analysis.PrincipalEnergy.Quantization.CompactQuantization

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open Set Filter MeasureTheory Burnett.Microlocal.AngularDyadicKernel
open scoped BigOperators FourierTransform Topology

private def fullFrequencyIntegrand (a : E → E → ℂ) (x : E) (f : SchwartzMap E ℂ) (ξ : E) : ℂ :=
  (Real.fourierChar (inner ℝ ξ x)) •
    (a x ξ * (SchwartzMap.fourierTransformCLM ℂ f) ξ)

private theorem fullFrequency_integrable (a : E → E → ℂ) (ha : FrequencyOrderOne a) (x : E)
    (f : SchwartzMap E ℂ) : Integrable (fullFrequencyIntegrand a x f) (volume : Measure E) := by
  obtain ⟨M,hM,hA⟩ := ha.order 0
  have hOrder (ξ : E) : ‖a x ξ‖ ≤ M * (1 + ‖ξ‖) := by
    simpa only [pow_zero, mul_one, norm_iteratedFDeriv_zero] using hA x ξ
  let F := SchwartzMap.fourierTransformCLM ℂ f
  have hM₁ := F.integrable.norm.add (F.integrable_pow_mul (volume : Measure E) 1)
  have hM₂ : Integrable (fun ξ : E => M * ((1 + ‖ξ‖) * ‖F ξ‖)) (volume : Measure E) := by
    simpa only [add_mul, one_mul, pow_one] using hM₁.const_mul M
  have hSym : Continuous (a x) := (ha.smooth x).continuous
  have hChar : Continuous (fun ξ : E => Real.fourierChar (inner ℝ ξ x)) :=
    Real.continuous_fourierChar.comp (continuous_id.inner continuous_const)
  apply hM₂.mono' (hChar.smul (hSym.mul F.continuous)).aestronglyMeasurable
  filter_upwards with ξ
  change ‖Real.fourierChar (inner ℝ ξ x) • (a x ξ * F ξ)‖ ≤ _
  rw [Circle.norm_smul, norm_mul, ← mul_assoc M]
  exact mul_le_mul_of_nonneg_right (hOrder ξ) (norm_nonneg _)

theorem firstOrderAction_sub_smul (a : E → E → ℂ) (ha : FrequencyOrderOne a) (x : E)
    (f g : SchwartzMap E ℂ) (c : ℂ) :
    firstOrderAction a (f - c • g : SchwartzMap E ℂ) x =
      firstOrderAction a f x - c * firstOrderAction a g x := by
  have h : fullFrequencyIntegrand a x (f - c • g) =
      fun ξ => fullFrequencyIntegrand a x f ξ - c • fullFrequencyIntegrand a x g ξ := by
    funext ξ
    simp only [fullFrequencyIntegrand, map_sub, map_smul, SchwartzMap.sub_apply, SchwartzMap.smul_apply,
      mul_sub, mul_smul_comm, smul_sub, smul_comm (Real.fourierChar _)]
  have heq (u : SchwartzMap E ℂ) : firstOrderAction a u x = ∫ ξ, fullFrequencyIntegrand a x u ξ := by
    rw [firstOrderAction, Real.fourierIntegralInv_eq]
    rfl
  rw [heq, h]
  change (∫ ξ, fullFrequencyIntegrand a x f ξ - (c • fullFrequencyIntegrand a x g) ξ) = _
  rw [integral_sub (fullFrequency_integrable a ha x f) ((fullFrequency_integrable a ha x g).smul c)]
  change (∫ ξ, fullFrequencyIntegrand a x f ξ) - (∫ ξ, c • fullFrequencyIntegrand a x g ξ) = _
  rw [integral_smul, ← heq, ← heq, smul_eq_mul]

/-- The compact base of the symbol gives an actual integrable full action on every
Schwartz input, in addition to its previously verified L² mapping. -/
theorem firstOrderAction_integrable_of_compactBase {a : E → E → ℂ}
    (ha : CompactBaseOrderOne a) (hc : Continuous (Function.uncurry a))
    (f : SchwartzMap E ℂ) : Integrable (firstOrderAction a f) := by
  obtain ⟨K,hK,hSupport⟩ := ha.support
  obtain ⟨_,_,hMap⟩ := exists_compactBase_firstOrderAction_h1_to_l2 ha hc
  obtain ⟨hB,_⟩ := hMap f
  letI : IsFiniteMeasure ((volume : Measure E).restrict K) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hInside : IntegrableOn (firstOrderAction a f) K :=
    MeasureTheory.MemLp.integrable (by norm_num : (1 : ENNReal) ≤ 2) (hB.restrict K)
  have hEq : K.indicator (firstOrderAction a f) = firstOrderAction a f := by
    funext x
    by_cases hx : x ∈ K
    · rw [indicator_of_mem hx]
    · have hA (ξ : E) : a x ξ = 0 := by
        by_contra h
        exact hx (hSupport ξ (subset_closure h))
      rw [indicator_of_notMem hx,firstOrderAction,Real.fourierIntegralInv_eq]
      simp only [hA,zero_mul,smul_zero,integral_zero]
  rw [← hEq]
  exact hInside.integrable_indicator hK.measurableSet

end Burnett.Analysis.FirstOrderDyadic
