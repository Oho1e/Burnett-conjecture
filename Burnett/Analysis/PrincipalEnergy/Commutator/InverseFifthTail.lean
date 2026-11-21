import Burnett.Analysis.PrincipalEnergy.Quantization.FirstOrderActionLimit
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

set_option autoImplicit false
noncomputable section

namespace Burnett.Analysis.FirstOrderDyadic

open MeasureTheory Filter Burnett.Microlocal.AngularDyadicKernel

def inverseFifthTail (R : ℝ) (z : E) : ℝ :=
  if R ≤ ‖z‖ then (‖z‖^5)⁻¹ else 0

theorem inverseFifthTail_nonneg (R : ℝ) (z : E) : 0 ≤ inverseFifthTail R z := by
  unfold inverseFifthTail
  split <;> positivity

/-- The cutoff inverse fifth power is integrable in four dimensions, with
the true cutoff at the prescribed radius. -/
theorem inverseFifthTail_integrable {R : ℝ} (hR : 0 < R) :
    Integrable (inverseFifthTail R) (volume : Measure E) := by
  have hr : (Module.finrank ℝ E : ℝ) < 5 := by norm_num [finrank_euclideanSpace_fin]
  let A := (1+R⁻¹)^5
  have hA : 0 ≤ A := by unfold A; positivity
  have hBase : Integrable (fun z : E => ((1+‖z‖)^5)⁻¹) := by
    apply (integrable_one_add_norm (μ := (volume : Measure E)) hr).congr
    filter_upwards with z
    rw [Real.rpow_neg (by positivity)]
    norm_num [Real.rpow_natCast]
  have hM : Measurable (inverseFifthTail R) := by
    unfold inverseFifthTail
    exact Measurable.ite (measurableSet_le measurable_const measurable_norm)
      (by fun_prop) measurable_const
  refine (hBase.const_mul A).mono' hM.aestronglyMeasurable (Eventually.of_forall fun z => ?_)
  rw [Real.norm_of_nonneg (inverseFifthTail_nonneg R z)]
  by_cases hz : R ≤ ‖z‖
  · rw [inverseFifthTail,if_pos hz, ← div_eq_mul_inv, ← one_div]
    have hP : 0 < ‖z‖ := hR.trans_le hz
    have hQ : 1 ≤ R⁻¹ * ‖z‖ := by
      rw [← div_eq_inv_mul]
      exact (le_div_iff₀ hR).mpr (by simpa using hz)
    have hCompare : 1 + ‖z‖ ≤ (1+R⁻¹)*‖z‖ := by nlinarith
    apply (div_le_div_iff₀ (pow_pos hP _) (pow_pos (by positivity : 0 < 1+‖z‖) _)).mpr
    rw [one_mul, show A * ‖z‖^5 = ((1+R⁻¹)*‖z‖)^5 by simp only [A,mul_pow]]
    exact pow_le_pow_left₀ (by positivity) hCompare 5
  · simp only [inverseFifthTail,if_neg hz]
    positivity

/-- Haar scaling makes the inverse-fifth tail integral exactly inverse linear
in the truncation radius. -/
theorem inverseFifthTail_integral_scale {R : ℝ} (hR : 0 < R) :
    (∫ z, inverseFifthTail R z) = R⁻¹ * ∫ z, inverseFifthTail 1 z := by
  have hScale (z : E) : inverseFifthTail R (R • z) = (R^5)⁻¹ * inverseFifthTail 1 z := by
    unfold inverseFifthTail
    rw [norm_smul,Real.norm_of_nonneg hR.le]
    have he : R ≤ R * ‖z‖ ↔ 1 ≤ ‖z‖ := by
      simpa only [mul_one] using (mul_le_mul_iff_right₀ hR : R*1 ≤ R*‖z‖ ↔ 1 ≤ ‖z‖)
    by_cases hz : 1 ≤ ‖z‖
    · simp only [if_pos hz,if_pos (he.mpr hz),mul_pow,mul_inv_rev,mul_comm]
    · simp only [if_neg hz,if_neg (mt he.mp hz),mul_zero]
  have hc := Measure.integral_comp_smul_of_nonneg (volume : Measure E) (inverseFifthTail R)
    R (hR := hR.le)
  rw [show Module.finrank ℝ E = 4 from finrank_euclideanSpace_fin] at hc
  simp only [hScale,integral_const_mul,smul_eq_mul] at hc
  have hp : R^4 ≠ 0 := pow_ne_zero _ hR.ne'
  calc
    _ = R^4 * ((R^4)⁻¹ * ∫ z, inverseFifthTail R z) := by
      rw [← mul_assoc,mul_inv_cancel₀ hp,one_mul]
    _ = R^4 * ((R^5)⁻¹ * ∫ z, inverseFifthTail 1 z) := by rw [hc]
    _ = _ := by field_simp [hR.ne']

theorem inverseFifthTail_about_center {R : ℝ} (hR : 0 < R) (c : E) :
    Integrable (fun y => inverseFifthTail R (c-y)) ∧
      (∫ y, inverseFifthTail R (c-y)) = R⁻¹ * ∫ z, inverseFifthTail 1 z := by
  have ht := (volume : Measure E).measurePreserving_sub_left c
  have hi := inverseFifthTail_integrable hR
  refine ⟨ht.integrable_comp_of_integrable hi,?_⟩
  rw [← integral_map ht.measurable.aemeasurable (by rw [ht.map_eq]; exact hi.aestronglyMeasurable),
      ht.map_eq,inverseFifthTail_integral_scale hR]

end Burnett.Analysis.FirstOrderDyadic
