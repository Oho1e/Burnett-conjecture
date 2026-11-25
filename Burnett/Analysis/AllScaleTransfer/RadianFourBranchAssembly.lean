import Burnett.Analysis.AllScaleTransfer.RadianTrilinearSymmetry
import Burnett.Analysis.AngularCaps.ComparableTriadAngle

set_option autoImplicit false
set_option maxHeartbeats 4800000

noncomputable section

namespace Burnett.A05

open MeasureTheory
open Burnett.A02.FrequencySplit
open Burnett.Analysis.ProjectiveNullCaps (lowSlotWeight comparableSlotWeight)
open Burnett.Analysis.CapFourier (radianTrilinearForm radianTrilinearWeight
  integrable_radianTrilinearWeight_of_bounded)

/-- The original three low-slot cutoffs and the complementary fourth
cutoff are evaluated on the same signed Fourier triad. -/
def radianFourBranchWeight (ϑ : ℝ → ℝ) (κ : ℝ) (i : Fin 4) (p : Joint) : ℝ :=
  let r := -(p.1+p.2)
  ![lowSlotWeight ϑ κ p.1 p.2 r,lowSlotWeight ϑ κ p.2 r p.1,
    lowSlotWeight ϑ κ r p.1 p.2,comparableSlotWeight ϑ κ p.1 p.2 r] i

def radianFourBranchSymbol (ϑ : ℝ → ℝ) (κ : ℝ) (m : Joint → ℂ) (i : Fin 4) (p : Joint) : ℂ :=
  (radianFourBranchWeight ϑ κ i p : ℂ) * m p

theorem radianFourBranchSymbol_sum (ϑ : ℝ → ℝ) (κ : ℝ) (m : Joint → ℂ) (p : Joint) :
    ∑ i : Fin 4, radianFourBranchSymbol ϑ κ m i p = m p := by
  simp only [radianFourBranchSymbol, ← Finset.sum_mul, ← Complex.ofReal_sum, radianFourBranchWeight,
    Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ, add_zero,
    comparableSlotWeight]
  push_cast
  ring

private theorem measurable_radianFourBranchWeight (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ)
    (κ : ℝ) (i : Fin 4) : Measurable (radianFourBranchWeight ϑ κ i) := by
  have lo (x y z : Joint → E) (hx : Measurable x) (hy : Measurable y) (hz : Measurable z) :
      Measurable (fun p => lowSlotWeight ϑ κ (x p) (y p) (z p)) := by
    unfold lowSlotWeight
    exact hϑ.comp ((hx.norm.pow_const _).div (measurable_const.mul ((hy.norm.pow_const _).add (hz.norm.pow_const _))))
  have hthird : Measurable (fun p : Joint => -(p.1+p.2)) := (measurable_fst.add measurable_snd).neg
  fin_cases i
  · exact lo _ _ _ measurable_fst measurable_snd hthird
  · exact lo _ _ _ measurable_snd hthird measurable_fst
  · exact lo _ _ _ hthird measurable_fst measurable_snd
  · exact ((measurable_const.sub (lo _ _ _ measurable_fst measurable_snd hthird)).sub
      (lo _ _ _ measurable_snd hthird measurable_fst)).sub (lo _ _ _ hthird measurable_fst measurable_snd)

private theorem norm_radianFourBranchWeight_le (ϑ : ℝ → ℝ)
    (hϑ : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ : ℝ) (i : Fin 4) (p : Joint) :
      ‖radianFourBranchWeight ϑ κ i p‖ ≤ 4 := by
  have lo (x y z : E) : ‖lowSlotWeight ϑ κ x y z‖ ≤ 1 := by
    unfold lowSlotWeight
    exact hϑ _ (by positivity)
  fin_cases i
  · exact (lo _ _ _).trans (by norm_num)
  · exact (lo _ _ _).trans (by norm_num)
  · exact (lo _ _ _).trans (by norm_num)
  · change ‖comparableSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2))‖ ≤ 4
    unfold comparableSlotWeight
    let p₁ := lowSlotWeight ϑ κ p.1 p.2 (-(p.1+p.2))
    let p₂ := lowSlotWeight ϑ κ p.2 (-(p.1+p.2)) p.1
    let p₃ := lowSlotWeight ϑ κ (-(p.1+p.2)) p.1 p.2
    change ‖1-p₁-p₂-p₃‖ ≤ 4
    have H : ‖1-p₁-p₂-p₃‖ ≤ ‖(1:ℝ)‖ + ‖p₁‖ + ‖p₂‖ + ‖p₃‖ :=
      (norm_sub_le _ _).trans (add_le_add_right
        ((norm_sub_le _ _).trans (add_le_add_right (norm_sub_le _ _) _)) _)
    have h₁ : ‖p₁‖ ≤ 1 := lo _ _ _
    have h₂ : ‖p₂‖ ≤ 1 := lo _ _ _
    have h₃ : ‖p₃‖ ≤ 1 := lo _ _ _
    have hn : ‖(1:ℝ)‖ = 1 := norm_one
    linarith only [H,h₁,h₂,h₃,hn]

theorem radianTrilinearForm_actual_four_branches (ϑ : ℝ → ℝ) (hϑ : Measurable ϑ)
    (hRange : ∀ t ≥ 0, ‖ϑ t‖ ≤ 1) (κ : ℝ)
    (m : Joint → ℂ) (hm : Measurable m) (B : ℝ) (hB : ∀ p, ‖m p‖ ≤ B)
    (f g h : SchwartzMap E ℂ) :
    radianTrilinearForm m f g h =
      ∑ i : Fin 4, radianTrilinearForm (radianFourBranchSymbol ϑ κ m i) f g h := by
  have weights_eq : (fun p => ∑ i : Fin 4, radianFourBranchSymbol ϑ κ m i p) = m :=
    funext (radianFourBranchSymbol_sum ϑ κ m)
  have inte (i : Fin 4) : Integrable (radianTrilinearWeight (radianFourBranchSymbol ϑ κ m i) f g h) := by
    have meas : Measurable (radianFourBranchSymbol ϑ κ m i) :=
      (Complex.continuous_ofReal.measurable.comp (measurable_radianFourBranchWeight ϑ hϑ κ i)).mul hm
    exact integrable_radianTrilinearWeight_of_bounded _ meas.aestronglyMeasurable (4*B)
      (fun p => by
        simp only [radianFourBranchSymbol,norm_mul,Complex.norm_real]
        exact mul_le_mul (norm_radianFourBranchWeight_le ϑ hRange κ i p) (hB p) (norm_nonneg _) (by norm_num))
      f g h
  calc
    _ = radianTrilinearForm (fun p => ∑ i : Fin 4, radianFourBranchSymbol ϑ κ m i p) f g h :=
      congrArg (fun n => radianTrilinearForm n f g h) weights_eq.symm
    _ = _ := radianTrilinearForm_sum Finset.univ _ f g h (fun i _ => inte i)

/-- Rotate the second and third low-slot contributions into the same
first-low convention, without changing any Fourier or tensor factor. -/
theorem radianTrilinearForm_rotate_low_branches (ϑ : ℝ → ℝ) (κ : ℝ) (m : Joint → ℂ)
    (f g h : SchwartzMap E ℂ) :
    radianTrilinearForm (radianFourBranchSymbol ϑ κ m 1) f g h =
      radianTrilinearForm (radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0) g h f ∧
    radianTrilinearForm (radianFourBranchSymbol ϑ κ m 2) f g h =
      radianTrilinearForm (radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0) h f g := by
  have e1 : (radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0) ∘ radianCycle =
      radianFourBranchSymbol ϑ κ m 1 := by
    funext p
    have hThird : -((radianCycle p).1 + (radianCycle p).2) = p.1 := by
      change -(p.2+ -(p.1+p.2)) = p.1
      abel
    simp only [radianFourBranchSymbol,radianFourBranchWeight,Function.comp_apply,
      Matrix.cons_val_zero,MeasurableEquiv.symm_apply_apply,hThird]
    rfl
  have e2 : radianFourBranchSymbol ϑ κ m 2 ∘ radianCycle =
      radianFourBranchSymbol ϑ κ (m ∘ radianCycle) 0 := by
    funext p
    have hThird : -((radianCycle p).1 + (radianCycle p).2) = p.1 := by
      change -(p.2+ -(p.1+p.2)) = p.1
      abel
    simp only [radianFourBranchSymbol,radianFourBranchWeight,Function.comp_apply,
      Matrix.cons_val_zero,hThird]
    rfl
  constructor
  · have h1 := radianTrilinearForm_cycle (radianFourBranchSymbol ϑ κ (m ∘ radianCycle.symm) 0) g h f
    rwa [e1] at h1
  · have h2 := radianTrilinearForm_cycle (radianFourBranchSymbol ϑ κ m 2) f g h
    rw [e2] at h2
    exact h2.symm

end Burnett.A05
