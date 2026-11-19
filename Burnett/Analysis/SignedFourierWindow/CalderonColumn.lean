import Burnett.Analysis.SignedFourierWindow.CalderonSplit
import Burnett.Analysis.SignedFourierWindow.SignedWindowOperator

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Metric Set
open scoped ENNReal

/-- Translation of the integral Hörmander condition to the center of a bad
block. Its fourfold supporting ball fits inside the eightfold exceptional ball. -/
theorem exterior_kernel_column (K : Space → ℂ) (A : ℝ≥0∞)
    (hK : ∀ h : Space, (∫⁻ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ A)
    (p y : Space) (r : ℝ) (hy : y ∈ closedBall p (4*r)) :
    (∫⁻ x in (closedBall p (8*r))ᶜ, ‖K (x-y)-K (x-p)‖ₑ) ≤ A := by
  let S := (closedBall p (8*r))ᶜ
  let T := {z : Space | 2*‖y-p‖ ≤ ‖z‖}
  let F := fun z : Space => ‖K (z-(y-p))-K z‖ₑ
  have hmS : MeasurableSet S := measurableSet_closedBall.compl
  have hmT : MeasurableSet T := (isClosed_le continuous_const continuous_norm).measurableSet
  have le (x : Space) : S.indicator (fun x => ‖K (x-y)-K (x-p)‖ₑ) x ≤ T.indicator F (x-p) := by
    by_cases hx : x ∈ S
    · have hdist : 8*r < ‖x-p‖ := by
        simpa only [S,mem_compl_iff,mem_closedBall,not_le,dist_eq_norm] using hx
      have hyd : ‖y-p‖ ≤ 4*r := by simpa only [mem_closedBall,dist_eq_norm] using hy
      have ht : x-p ∈ T := by change 2*‖y-p‖ ≤ ‖x-p‖; linarith
      rw [indicator_of_mem hx,indicator_of_mem ht]
      simp only [F,sub_sub_sub_cancel_right,le_refl]
    · rw [indicator_of_notMem hx]
      exact zero_le _
  rw [← lintegral_indicator hmS]
  refine (lintegral_mono le).trans ?_
  have translate := (measurePreserving_add_right (volume : Measure Space) (-p)).lintegral_comp_emb
    (Homeomorph.addRight (-p)).measurableEmbedding (T.indicator F)
  change (∫⁻ x : Space, T.indicator F (x-p)) ≤ A
  simpa only [sub_eq_add_neg] using translate.trans_le (by
    rw [lintegral_indicator hmT]; exact hK (y-p))

/-- Pass from the real-valued integral used by the physical kernel estimates
to the extended norm integral needed for Tonelli. -/
theorem kernel_hormander_enorm (K : Space → ℂ) (hI : Integrable K) (C : ℝ)
    (bound : ∀ h : Space, (∫ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖) ≤ C) (h : Space) :
    (∫⁻ z in {z : Space | 2*‖h‖ ≤ ‖z‖}, ‖K (z-h)-K z‖ₑ) ≤ ENNReal.ofReal C := by
  have ht : Integrable (fun z : Space => K (z-h)) := by
    simpa only [sub_eq_add_neg] using ((measurePreserving_add_right (volume : Measure Space) (-h)).integrable_comp_emb
      (Homeomorph.addRight (-h)).measurableEmbedding).2 hI
  have hi : IntegrableOn (fun z : Space => K (z-h)-K z) {z : Space | 2*‖h‖ ≤ ‖z‖} :=
    (ht.sub hI).integrableOn
  exact (ofReal_integral_norm_eq_lintegral_enorm hi).symm.trans_le (ENNReal.ofReal_le_ofReal (bound h))

end Burnett.Analysis.SignedFourierWindow
