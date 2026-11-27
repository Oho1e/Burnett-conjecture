import Burnett.Analysis.PrincipalEnergy.Freezing.EnergyHolder
import Burnett.Analysis.CubicEnergy.BilinearMultiplier.CMBilinearDual

set_option autoImplicit false
set_option maxHeartbeats 1400000
noncomputable section

namespace Burnett.A03

open Filter MeasureTheory Function Burnett.A02.FrequencySplit
open scoped ENNReal

/-- Integrated physical L³ estimates for a measurable parameter family. The
pointwise majorant is used for Fubini. The L³ bound uses only the supplied
operator norms and the integral of their scalar weight. -/
theorem patch_integral_L3_bound {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [SFinite μ]
    (G : α × E → ℂ) (hG : Measurable G) (A : E → ℂ) (hA : Continuous A)
    (action : ∀ x, A x = ∫ t, G (t, x) ∂μ)
    (w : α → ℝ) (hw : Integrable w μ) (w0 : ∀ t, 0 ≤ w t)
    (M : ℝ) (majorant : ∀ t x, ‖G (t, x)‖ ≤ w t * M)
    (V : ℝ≥0∞) (hV : V < ⊤)
    (est : ∀ t, MemLp (fun x => G (t, x)) (ENNReal.ofReal 3) volume ∧
      eLpNorm (fun x => G (t, x)) (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (w t) * V) :
    MemLp A (ENNReal.ofReal 3) volume ∧
      eLpNorm A (ENNReal.ofReal 3) volume ≤ ENNReal.ofReal (∫ t, w t ∂μ) * V := by
  have conjugate : Real.HolderConjugate 3 (3 / 2) := by
    constructor <;> norm_num
  apply CMBilinearDual.memLp_of_schwartz_pairing conjugate hA
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hV).ne
  intro φ
  let p := ENNReal.ofReal (3 / 2)
  let P := eLpNorm (φ : E → ℂ) p volume
  let F : α × E → ℂ := fun z => G z * φ z.2
  have hF : Integrable F (μ.prod (volume : Measure E)) := by
    apply ((hw.mul_const M).mul_prod φ.integrable.norm).mono'
      (hG.mul (φ.continuous.measurable.comp measurable_snd)).aestronglyMeasurable
    filter_upwards with z
    exact (norm_mul _ _).trans_le (mul_le_mul_of_nonneg_right (majorant _ _) (norm_nonneg _))
  have pair (t : α) : ‖∫ x, F (t, x)‖ₑ ≤ ENNReal.ofReal (w t) * (V * P) := by
    have h := (energy_integral_three_three_halves (est t).1 (φ.memLp p volume)).2
    exact h.trans (((mul_le_mul_right' (est t).2 P)).trans_eq (mul_assoc ..))
  calc
    _ = ‖∫ t, (∫ x, F (t, x)) ∂μ‖ₑ := by
      congr 1
      calc
        _ = ∫ x, (∫ t, F (t, x) ∂μ) := by
          apply integral_congr_ae
          filter_upwards with x
          rw [action x, ← integral_mul_const]
        _ = _ := (integral_integral_swap (f := fun t x => F (t, x)) hF).symm
    _ ≤ ∫⁻ t, ‖∫ x, F (t, x)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ t, ENNReal.ofReal (w t) * (V * P) ∂μ := lintegral_mono pair
    _ = _ := by
      have hm : AEMeasurable (fun t => ENNReal.ofReal (w t)) μ :=
        ENNReal.measurable_ofReal.comp_aemeasurable hw.aestronglyMeasurable.aemeasurable
      calc
        _ = (∫⁻ t, ENNReal.ofReal (w t) ∂μ) * (V * P) :=
          lintegral_mul_const'' (V * P) hm
        _ = _ := by
          rw [← ofReal_integral_eq_lintegral_ofReal hw (Eventually.of_forall w0)]
          exact (mul_assoc _ _ _).symm

end Burnett.A03
