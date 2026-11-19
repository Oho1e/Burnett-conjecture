import Burnett.Analysis.CenteredMaximal.MaximalMeasurable
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal
open MeasureTheory Set
open scoped ENNReal

/-- The distribution-function formula for all positive powers, including
the exponent p−1 used after the maximal-function truncation. -/
theorem power_distribution {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (f : α → ℝ) (hm : Measurable f) (hn : ∀ x, 0 ≤ f x) (q : ℝ) (hq : 0<q) :
    (∫⁻ x, ENNReal.ofReal ((f x)^q / q) ∂μ) =
    ∫⁻ t in Ioi (0:ℝ), μ {x | t < f x} * ENNReal.ofReal (t^(q-1)) := by
  have h := lintegral_comp_eq_lintegral_meas_lt_mul (g := fun t : ℝ => t^(q-1)) μ
    (Filter.Eventually.of_forall hn) hm.aemeasurable
    (fun _ _ => intervalIntegral.intervalIntegrable_rpow' (by linarith))
    (by filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
        exact Real.rpow_nonneg (le_of_lt ht) _)
  simpa only [integral_rpow (Or.inl (by linarith : -1 < q-1)),sub_add_cancel,
    Real.zero_rpow hq.ne',sub_zero] using h

/-- Integrating the truncated L¹ input from the weak estimate costs exactly
one power of the height. The weighted measure is g(x) dx. -/
theorem integrated_tail_power (g : Space → ℝ) (hm : Measurable g) (hn : ∀ x, 0 ≤ g x)
    (q : ℝ) (hq : 0<q) :
    (∫⁻ t in Ioi (0:ℝ), (∫⁻ x, upperTail (fun y => ENNReal.ofReal (g y)) (ENNReal.ofReal t) x) *
        ENNReal.ofReal (t^(q-1))) =
      ∫⁻ x, ENNReal.ofReal (g x) * ENNReal.ofReal ((g x)^q / q) := by
  let G := fun x => ENNReal.ofReal (g x)
  have hG : Measurable G := ENNReal.measurable_ofReal.comp hm
  let ν := (volume : Measure Space).withDensity G
  have hmass (t : ℝ) (ht : 0<t) : ν {x | t < g x} =
      ∫⁻ x, upperTail G (ENNReal.ofReal t) x := by
    rw [show ν = (volume : Measure Space).withDensity G from rfl,
      withDensity_apply _ (measurableSet_lt measurable_const hm),
      ← lintegral_indicator (measurableSet_lt measurable_const hm)]
    apply lintegral_congr
    intro x
    by_cases h : t < g x
    · have h' : ENNReal.ofReal t < G x := (ENNReal.ofReal_lt_ofReal_iff (ht.trans h)).2 h
      simp [upperTail,h',h]
    · have h' : ¬ ENNReal.ofReal t < G x := not_lt_of_ge (ENNReal.ofReal_le_ofReal (le_of_not_gt h))
      simp [upperTail,h',h]
  have hlevel : (∫⁻ t in Ioi (0:ℝ), (∫⁻ x, upperTail G (ENNReal.ofReal t) x) * ENNReal.ofReal (t^(q-1))) =
      ∫⁻ t in Ioi (0:ℝ), ν {x | t < g x} * ENNReal.ofReal (t^(q-1)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioi] with t ht
    rw [hmass t ht]
  rw [hlevel,← power_distribution ν g hm hn q hq]
  exact lintegral_withDensity_eq_lintegral_mul _ hG (by fun_prop)

end Burnett.Analysis.CenteredMaximal
