import Burnett.Analysis.PrincipalEnergy.Quantization.LowFrequencyCommutator

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Microlocal.AngularDyadicKernel

/-- The actual low-frequency action has a uniform pointwise estimate on
bounded Schwartz inputs, using the same integrable spatial kernel majorant. -/
theorem exists_lowAction_sup_bound {a : E → E → ℂ} (ha : FrequencyOrderOne a) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (r : SchwartzMap E ℂ) (U : ℝ), 0 ≤ U →
      (∀ y, ‖r y‖ ≤ U) → ∀ x, ‖firstOrderLowAction a r x‖ ≤ D*U := by
  obtain ⟨C,hC,hI,hBound⟩ := exists_lowKernel_integrable_profile ha
  let env (z : E) := C*((1+‖z‖^2)^3)⁻¹
  refine ⟨∫ z, env z,integral_nonneg (fun z => by dsimp [env]; positivity),?_⟩
  intro r U hU hr x
  rw [firstOrderLowAction_eq_kernel ha r r.integrable]
  have ht := (volume : Measure E).measurePreserving_sub_left x
  have hI' : Integrable (fun y => env (x-y)) := ht.integrable_comp_of_integrable hI
  have hEq : (∫ y, env (x-y)) = ∫ z, env z := by
    rw [← integral_map ht.measurable.aemeasurable (by rw [ht.map_eq]; exact hI.aestronglyMeasurable), ht.map_eq]
  calc
    _ ≤ ∫ y, ‖firstOrderLowKernel a x (x-y)*r y‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y, U*env (x-y) := integral_mono_of_nonneg
      (Eventually.of_forall fun _ => norm_nonneg _) (hI'.const_mul U)
      (Eventually.of_forall fun y => by
        change ‖firstOrderLowKernel a x (x-y) * r y‖ ≤ U * env (x-y)
        rw [norm_mul,mul_comm U]
        exact mul_le_mul (hBound x (x-y)) (hr y) (norm_nonneg _) (by dsimp [env]; positivity))
    _ = _ := by rw [integral_const_mul,hEq,mul_comm]

end Burnett.Analysis.FirstOrderDyadic
