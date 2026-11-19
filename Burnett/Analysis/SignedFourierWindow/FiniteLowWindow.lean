import Burnett.Analysis.SignedFourierWindow.AnnularSquareLp
import Burnett.Analysis.ShiftedFourierWindow.LowPassLp

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space
open Burnett.Analysis.ShiftedFourierWindow
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open Finset MeasureTheory
open scoped NNReal ENNReal

def finiteAmplitude {n : ℕ} (u : Fin n → Space → ℂ) (x : Space) : ℝ :=
  ↑(Finset.univ.sup (fun i => ‖u i x‖₊))

theorem measurable_finiteAmplitude {n : ℕ} (u : Fin n → Space → ℂ) (hm : ∀ i, Measurable (u i)) :
    Measurable (finiteAmplitude u) := by
  classical
  have sub (I : Finset (Fin n)) : Measurable (fun x => I.sup (fun i => ‖u i x‖₊)) := by
    induction I using Finset.induction_on with
    | empty => simpa only [sup_empty] using (measurable_const (a := (⊥:ℝ≥0)))
    | insert i I _ ih =>
      simp only [sup_insert]
      exact (hm i).nnnorm.sup ih
  exact NNReal.continuous_coe.measurable.comp (sub univ)

theorem finite_low_domination {n : ℕ} (a f : SchwartzMap Space ℂ) (q : Space) (s : Fin n → ℝ)
    (hs : ∀ i, 0<s i) :
    ∀ x, ‖finiteAmplitude (fun i => shiftedWindowOperator a f (s i) q) x‖ₑ ≤ maximalShiftedWindow a f q x := by
  classical
  intro x
  let u := fun i : Fin n => ‖shiftedWindowOperator a f (s i) q x‖₊
  have sub (I : Finset (Fin n)) : (↑(I.sup u) : ℝ≥0∞) ≤ maximalShiftedWindow a f q x := by
    induction I using Finset.induction_on with
    | empty => simp [zero_le]
    | insert i I _ ih =>
      rw [sup_insert]
      rcases le_total (u i) (I.sup u) with h|h
      · rwa [sup_of_le_right h]
      · rw [sup_of_le_left h]
        exact le_iSup (fun j : {z : ℝ // 0<z} => ‖shiftedWindowOperator a f j q x‖ₑ) ⟨s i,hs i⟩
  change ‖((univ.sup u : ℝ≥0):ℝ)‖ₑ ≤ _
  rw [Real.enorm_eq_ofReal (NNReal.coe_nonneg _),ENNReal.ofReal_coe_nnreal]
  exact sub univ

theorem finite_low_window_Lp (a : SchwartzMap Space ℂ) (p : ℝ) (hp : 1<p) :
    ∃ C : ℝ≥0∞, C<⊤ ∧ ∀ (f : SchwartzMap Space ℂ) (q : Space) (n : ℕ) (s : Fin n → ℝ),
      (∀ i, 0<s i) → eLpNorm (finiteAmplitude (fun i => shiftedWindowOperator a f (s i) q))
        (ENNReal.ofReal p) volume ≤ (C*ENNReal.ofReal ((1+‖q‖)^5))*eLpNorm (f : Space → ℂ) (ENNReal.ofReal p) volume := by
  obtain ⟨C,hfin,H⟩ := maximalShiftedWindow_Lp a
  have ip : 0≤1/p := by positivity
  refine ⟨C*(maximalConstant p)^(1/p),ENNReal.mul_lt_top hfin
    (ENNReal.rpow_lt_top_of_nonneg ip (maximalConstant_finite p).ne),?_⟩
  intro f q n s hs
  exact (eLpNorm_mono_enorm (finite_low_domination a f q s hs)).trans
    ((H f q p hp).trans_eq (by ac_rfl))

end Burnett.Analysis.SignedFourierWindow
