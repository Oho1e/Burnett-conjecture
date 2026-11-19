import Burnett.Analysis.SignedFourierWindow.CalderonDifferentiation

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set
open scoped ENNReal

def badBlock (f : Space → ℂ) (Q : Set Space) : Space → ℂ := Q.indicator (fun z => f z - ⨍ y in Q, f y)

theorem bad_block_integral (f : Space → ℂ) (hf : Integrable f) (Q : Set Space) (hQ : MeasurableSet Q)
    (hfin : volume Q < ⊤) :
    Integrable (badBlock f Q) ∧ (∫ z, badBlock f Q z) = 0 ∧
      (∫ z, ‖badBlock f Q z‖) ≤ 2*∫ z in Q, ‖f z‖ := by
  let m := ⨍ y in Q,f y
  letI : Fact (volume Q < ⊤) := ⟨hfin⟩
  have hc : IntegrableOn (fun _ : Space => m) Q := integrable_const _
  have hd : IntegrableOn (fun z => f z - m) Q := hf.integrableOn.sub hc
  have hm : volume.real Q * ‖m‖ ≤ ∫ z in Q, ‖f z‖ := by
    rw [← Real.norm_of_nonneg (measureReal_nonneg : 0 ≤ volume.real Q),← norm_smul,
      show volume.real Q • m = ∫ z in Q, f z from measure_smul_setAverage f hfin.ne]
    exact norm_integral_le_integral_norm _
  refine ⟨(integrable_indicator_iff hQ).mpr hd, ?_, ?_⟩
  · rw [badBlock,integral_indicator hQ]
    exact setAverage_sub_setAverage hfin.ne f
  · have he (z : Space) : ‖badBlock f Q z‖ = Q.indicator (fun y => ‖f y - m‖) z := by
      by_cases hz : z ∈ Q <;> simp [badBlock,hz,m]
    simp_rw [he]
    rw [integral_indicator hQ]
    have bound := integral_mono hd.norm (hf.norm.integrableOn.add hc.norm)
      (fun z : Space => norm_sub_le (f z) m)
    change (∫ z in Q, ‖f z-m‖) ≤ ∫ z in Q, ‖f z‖+‖m‖ at bound
    rw [integral_add hf.norm.integrableOn hc.norm, setIntegral_const,smul_eq_mul] at bound
    linarith

theorem bounded_region_average (f : Space → ℂ) (Q : Set Space) (hpos : 0 < volume Q) (hfin : volume Q < ⊤)
    (a : ℝ≥0∞) (h : (∫⁻ y in Q, ‖f y‖ₑ) ≤ a*(256*volume Q)) :
    ‖⨍ y in Q, f y‖ₑ ≤ a*256 := by
  let m := ⨍ y in Q,f y
  have mul : ‖m‖ₑ * volume Q = ‖∫ y in Q, f y‖ₑ := by
    rw [← measure_smul_setAverage f hfin.ne,← ofReal_norm_eq_enorm (volume.real Q • m),norm_smul,
      Real.norm_of_nonneg (measureReal_nonneg : 0 ≤ volume.real Q),
      ENNReal.ofReal_mul measureReal_nonneg,measureReal_def,ENNReal.ofReal_toReal hfin.ne,
      ofReal_norm_eq_enorm,mul_comm]
  have hb := (enorm_integral_le_lintegral_enorm (μ := volume.restrict Q) f).trans h
  rw [← mul,← mul_assoc] at hb
  exact (ENNReal.mul_le_mul_right hpos.ne' hfin.ne).mp hb

end Burnett.Analysis.SignedFourierWindow
