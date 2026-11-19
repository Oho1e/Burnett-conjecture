import Burnett.Analysis.SignedFourierWindow.CalderonWeakEstimate

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set
open scoped ENNReal

/-- Split the input at its own height. The high contribution has exactly the
L¹ tail mass and the low contribution has exactly the truncated square mass. -/
theorem kernel_height_split (K : Space → ℂ) (hK : Continuous K) (D : ℝ) (hD : ∀ z, ‖K z‖ ≤ D)
    (f : Space → ℂ) (hm : Measurable f) (hf : Integrable f) (t : ℝ) (ht : 0<t) :
    ∃ (h l : Space → ℂ), Integrable h ∧ Measurable l ∧ MemLp l 2 volume ∧
      (∀ x, kernelApply K f x = kernelApply K h x + kernelApply K l x) ∧
      (∫⁻ x, ‖h x‖ₑ) = (∫⁻ x, upperTail (fun y => ENNReal.ofReal ‖f y‖) (ENNReal.ofReal t) x) ∧
      (eLpNorm l 2 volume)^2 = ∫⁻ x in {x : Space | ‖f x‖ ≤ t}, (ENNReal.ofReal ‖f x‖)^2 := by
  classical
  let H := {x : Space | t < ‖f x‖}
  let L := {x : Space | ‖f x‖ ≤ t}
  have hmH : MeasurableSet H := measurableSet_lt measurable_const hm.norm
  have hmL : MeasurableSet L := measurableSet_le hm.norm measurable_const
  let h := H.indicator f
  let l := L.indicator f
  have hi : Integrable h := hf.indicator hmH
  have li : Integrable l := hf.indicator hmL
  have lm : Measurable l := hm.indicator hmL
  have bound (x : Space) : ‖l x‖ ≤ t := by
    by_cases hx : x ∈ L
    · simpa only [l,indicator_of_mem hx] using hx
    · simpa only [l,indicator_of_notMem hx,norm_zero] using ht.le
  have l2 : MemLp l 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm lm.aestronglyMeasurable).mpr ?_
    apply (li.norm.const_mul t).mono' (lm.norm.pow_const 2).aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_of_nonneg (sq_nonneg _),pow_two]
    exact mul_le_mul_of_nonneg_right (bound x) (norm_nonneg _)
  refine ⟨h,l,hi,lm,l2,?_,?_,?_⟩
  · intro x
    have point (y : Space) : K (x-y)*f y = K (x-y)*h y + K (x-y)*l y := by
      by_cases hit : t < ‖f y‖
      · simp [h,l,H,L,hit,not_le.mpr hit]
      · simp [h,l,H,L,hit,not_lt.mp hit]
    unfold kernelApply
    simp_rw [point]
    exact integral_add (kernel_integrand K hK D hD hi x) (kernel_integrand K hK D hD li x)
  · refine lintegral_congr fun x => ?_
    by_cases hit : t < ‖f x‖
    · have hh := (ENNReal.ofReal_lt_ofReal_iff (ht.trans hit)).2 hit
      change ‖h x‖ₑ = if ENNReal.ofReal t < ENNReal.ofReal ‖f x‖ then ENNReal.ofReal ‖f x‖ else 0
      rw [if_pos hh,show h x = f x from indicator_of_mem (show x ∈ H from hit) f,ofReal_norm_eq_enorm]
    · have hh : ¬ ENNReal.ofReal t < ENNReal.ofReal ‖f x‖ := not_lt_of_ge (ENNReal.ofReal_le_ofReal (not_lt.mp hit))
      simp only [h,indicator_of_notMem (show x ∉ H from hit),upperTail,if_neg hh,enorm_zero]
  · have eq : eLpNorm l 2 volume ^ 2 = ∫⁻ x, ‖l x‖ₑ^2 := by
      simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure Space)) (f := l) (p := 2) (by norm_num)
    rw [eq,← lintegral_indicator hmL]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ L <;> simp [l,hx]

end Burnett.Analysis.SignedFourierWindow
