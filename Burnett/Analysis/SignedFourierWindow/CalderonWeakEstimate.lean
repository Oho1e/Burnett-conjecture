import Burnett.Analysis.SignedFourierWindow.CalderonEnergy
import Burnett.Analysis.SignedFourierWindow.CalderonBadSum
import Mathlib.MeasureTheory.Function.LpSeminorm.ChebyshevMarkov

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set
open scoped ENNReal

private theorem sq_eLp (f : Space → ℂ) : eLpNorm f 2 volume ^ 2 = ∫⁻ x, ‖f x‖ₑ^2 := by
  simpa using eLpNorm_nnreal_pow_eq_lintegral (μ := (volume : Measure Space)) (f := f) (p := 2) (by norm_num)

/-- L² Chebyshev on the good output, L¹ Chebyshev off the exceptional set on
the bad output, using the same positive level in both estimates. -/
theorem weak_from_good_bad (F G : Space → ℂ) (hmf : Measurable F) (hmg : Measurable G)
    (V : Set Space) (a M B A : ℝ≥0∞) (ha : 0 < a) (hfin : a < ⊤)
    (exc : a * volume V ≤ 4096*M)
    (good : eLpNorm G 2 volume ^ 2 ≤ B^2*((a*768)*M))
    (bad : (∫⁻ x in Vᶜ, ‖F x-G x‖ₑ) ≤ A*(2*M)) :
    a * volume {x | 2*a < ‖F x‖ₑ} ≤ (4096 + 768*B^2 + 2*A)*M := by
  let H := {x : Space | a ≤ ‖G x‖ₑ}
  let J := {x : Space | a ≤ ‖F x-G x‖ₑ}
  have hmJ : MeasurableSet J := measurableSet_le measurable_const (hmf.sub hmg).enorm
  have gcheb : a^2*volume H ≤ eLpNorm G 2 volume ^ 2 := by
    simpa only [H,ENNReal.toReal_ofNat,ENNReal.rpow_two] using
      mul_meas_ge_le_pow_eLpNorm' (volume : Measure Space) (p := 2) (by norm_num) (by norm_num) hmg.aestronglyMeasurable a
  have gsmall : a*volume H ≤ (768*B^2)*M := by
    apply (ENNReal.mul_le_mul_left ha.ne' hfin.ne).mp
    calc
      a*(a*volume H) = a^2*volume H := by ring
      _ ≤ _ := gcheb.trans good
      _ = a*((768*B^2)*M) := by ring
  have bsmall : a*volume (J ∩ Vᶜ) ≤ A*(2*M) := by
    have h := mul_meas_ge_le_lintegral (μ := volume.restrict Vᶜ) (hmf.sub hmg).enorm a
    change a*(volume.restrict Vᶜ) J ≤ _ at h
    rw [Measure.restrict_apply hmJ] at h
    exact h.trans bad
  have cover : {x : Space | 2*a < ‖F x‖ₑ} ⊆ (V ∪ H) ∪ (J ∩ Vᶜ) := by
    intro x hx
    by_cases hV : x ∈ V
    · exact Or.inl (Or.inl hV)
    by_cases hG : x ∈ H
    · exact Or.inl (Or.inr hG)
    refine Or.inr ⟨?_,hV⟩
    by_contra hJ
    have ht : ‖F x‖ₑ ≤ ‖G x‖ₑ + ‖F x-G x‖ₑ := by
      simpa only [show G x+(F x-G x) = F x by abel] using enorm_add_le (G x) (F x-G x)
    have le₁ : ‖G x‖ₑ ≤ a := (not_le.mp hG).le
    have le₂ : ‖F x-G x‖ₑ ≤ a := (not_le.mp hJ).le
    exact (not_lt_of_ge ((ht.trans (add_le_add le₁ le₂)).trans_eq (two_mul a).symm)) hx
  calc
    _ ≤ a*((volume V+volume H)+volume (J∩Vᶜ)) := mul_le_mul_left'
      ((measure_mono cover).trans ((measure_union_le _ _).trans (add_le_add_right (measure_union_le _ _) _))) _
    _ = a*volume V+a*volume H+a*volume (J∩Vᶜ) := by ring
    _ ≤ 4096*M+(768*B^2)*M+A*(2*M) := add_le_add (add_le_add exc gsmall) bsmall
    _ = _ := by ring

theorem good_output_energy (g G : Space → ℂ) (a M B : ℝ≥0∞)
    (h : eLpNorm G 2 volume ≤ B*eLpNorm g 2 volume)
    (e : (∫⁻ x, ‖g x‖ₑ^2) ≤ (a*768)*M) :
    eLpNorm G 2 volume ^ 2 ≤ B^2*((a*768)*M) := by
  calc
    _ ≤ (B*eLpNorm g 2 volume)^2 := pow_le_pow_left' h _
    _ = B^2*(∫⁻ x, ‖g x‖ₑ^2) := by rw [mul_pow,sq_eLp]
    _ ≤ _ := mul_le_mul_left' e _

end Burnett.Analysis.SignedFourierWindow
