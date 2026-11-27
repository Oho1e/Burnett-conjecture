import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Integral.Bochner.Basic

set_option autoImplicit false
noncomputable section

namespace Burnett.A02.FrequencySplit

open MeasureTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

private theorem energy_product_eLpNorm_bound {p q r : ℝ≥0∞} [ENNReal.HolderTriple p q r]
    {u v : α → ℂ} (hu : AEStronglyMeasurable u μ) (hv : AEStronglyMeasurable v μ) :
    eLpNorm (fun x => u x * v x) r μ ≤ eLpNorm u p μ * eLpNorm v q μ :=
  eLpNorm_smul_le_mul_eLpNorm (φ := u) (f := v) (p := p) (q := q) (r := r) hv hu

private theorem energy_integral_mul_holder {p q : ℝ≥0∞} [ENNReal.HolderTriple p q 1]
    {u v : α → ℂ} (hu : MemLp u p μ) (hv : MemLp v q μ) :
    Integrable (fun x => u x * v x) μ ∧
      ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u p μ * eLpNorm v q μ := by
  refine ⟨hu.integrable_mul hv, (enorm_integral_le_lintegral_enorm _).trans ?_⟩
  rw [← eLpNorm_one_eq_lintegral_enorm]
  exact energy_product_eLpNorm_bound hu.1 hv.1

private theorem energy_holder_three_three :
    ENNReal.HolderTriple (ENNReal.ofReal 3) (ENNReal.ofReal 3) (ENNReal.ofReal (3 / 2)) := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  exact congrArg ENNReal.ofReal (by norm_num)

private theorem energy_holder_three_halves_three :
    ENNReal.HolderTriple (ENNReal.ofReal (3 / 2)) (ENNReal.ofReal 3) 1 := by
  constructor
  rw [← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3 / 2),
    ← ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 3),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num), inv_one, ← ENNReal.ofReal_one]
  exact congrArg ENNReal.ofReal (by norm_num)

/-- Actual Bochner integrals for the coefficient-commutator slot. -/
theorem energy_integral_three_three_halves {u v : α → ℂ}
    (hu : MemLp u (ENNReal.ofReal 3) μ) (hv : MemLp v (ENNReal.ofReal (3 / 2)) μ) :
    Integrable (fun x => u x * v x) μ ∧
      ‖∫ x, u x * v x ∂μ‖ₑ ≤ eLpNorm u (ENNReal.ofReal 3) μ *
        eLpNorm v (ENNReal.ofReal (3 / 2)) μ := by
  letI := energy_holder_three_halves_three
  exact energy_integral_mul_holder hu hv

/-- Actual Bochner integrals for the three (L^3) factors in the two value slots. -/
theorem energy_integral_three_factors {u v w : α → ℂ}
    (hu : MemLp u (ENNReal.ofReal 3) μ) (hv : MemLp v (ENNReal.ofReal 3) μ)
    (hw : MemLp w (ENNReal.ofReal 3) μ) :
    Integrable (fun x => u x * v x * w x) μ ∧
      ‖∫ x, u x * v x * w x ∂μ‖ₑ ≤
        eLpNorm u (ENNReal.ofReal 3) μ * eLpNorm v (ENNReal.ofReal 3) μ *
          eLpNorm w (ENNReal.ofReal 3) μ := by
  letI := energy_holder_three_three
  letI := energy_holder_three_halves_three
  have huv : MemLp (fun x => u x * v x) (ENNReal.ofReal (3 / 2)) μ := hv.mul' hu
  obtain ⟨hi, h⟩ := energy_integral_mul_holder huv hw
  exact ⟨hi, h.trans (mul_le_mul_right' (energy_product_eLpNorm_bound hu.1 hv.1) _)⟩

end Burnett.A02.FrequencySplit
