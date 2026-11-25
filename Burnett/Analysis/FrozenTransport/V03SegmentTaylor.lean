import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Module
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-! Taylor coefficients along a segment in the actual metric field variables. -/

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxSize 2000
set_option synthInstance.maxHeartbeats 300000

noncomputable section

namespace Burnett.V03

open MeasureTheory Set
open scoped ContDiff Interval Topology

variable {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- The normalized affine segment in the field variables. -/
def fieldSegment (g h : V) (t : ℝ) : V := g + t • h

/-- The second Fréchet derivative, with the differentiating direction first. -/
abbrev secondFDeriv (F : V → W) := fderiv ℝ (fderiv ℝ F)

/-- The third Fréchet derivative, with the differentiating direction first. -/
abbrev thirdFDeriv (F : V → W) := fderiv ℝ (secondFDeriv F)

/-- Defect after subtracting the value and the full linear term. -/
def linearTaylorRemainder (F : V → W) (g h : V) : W :=
  F (g + h) - F g - fderiv ℝ F g h

/-- Defect after subtracting the full quadratic Taylor polynomial. -/
def quadraticTaylorRemainder (F : V → W) (g h : V) : W :=
  linearTaylorRemainder F g h - (1 / 2 : ℝ) • secondFDeriv F g h h

private theorem hasDerivAt_fieldSegment (g h : V) (t : ℝ) :
    HasDerivAt (fieldSegment g h) h t := by
  simpa only [fieldSegment, id_eq, one_smul] using ((hasDerivAt_id t).smul_const h).const_add g

private theorem hasDerivAt_comp_fieldSegment (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V) (t : ℝ)
    (ht : fieldSegment g h t ∈ U) :
    HasDerivAt (fun s => F (fieldSegment g h s)) (fderiv ℝ F (fieldSegment g h t) h) t := by
  have hD := (hF.contDiffAt (hU.mem_nhds ht)).differentiableAt (by simp)
  exact hD.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_fieldSegment g h t)

private theorem hasDerivAt_first_dir (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V) (t : ℝ)
    (ht : fieldSegment g h t ∈ U) :
    HasDerivAt (fun s => fderiv ℝ F (fieldSegment g h s) h)
      (secondFDeriv F (fieldSegment g h t) h h) t :=
  (ContinuousLinearMap.apply ℝ W h).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_comp_fieldSegment (fderiv ℝ F) hU (hF.fderiv_of_isOpen hU (by simp)) g h t ht)

private theorem hasDerivAt_second_dir (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V) (t : ℝ)
    (ht : fieldSegment g h t ∈ U) :
    HasDerivAt (fun s => secondFDeriv F (fieldSegment g h s) h h)
      (thirdFDeriv F (fieldSegment g h t) h h h) t :=
  (ContinuousLinearMap.apply ℝ W h).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_first_dir (fderiv ℝ F) hU (hF.fderiv_of_isOpen hU (by simp)) g h t ht)

private theorem hasDerivAt_third_dir (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V) (t : ℝ)
    (ht : fieldSegment g h t ∈ U) :
    HasDerivAt (fun s => thirdFDeriv F (fieldSegment g h s) h h h)
      (fderiv ℝ (thirdFDeriv F) (fieldSegment g h t) h h h h) t :=
  (ContinuousLinearMap.apply ℝ W h).hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_second_dir (fderiv ℝ F) hU (hF.fderiv_of_isOpen hU (by simp)) g h t ht)

variable [CompleteSpace W]

theorem sub_eq_integral_first_dir (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U) :
    F (g + h) - F g = ∫ t in (0 : ℝ)..1, fderiv ℝ F (fieldSegment g h t) h := by
  have hD : ∀ t ∈ uIcc (0 : ℝ) 1,
      HasDerivAt (fun s => F (fieldSegment g h s)) (fderiv ℝ F (fieldSegment g h t) h) t := by
    rw [uIcc_of_le zero_le_one]
    exact fun t ht => hasDerivAt_comp_fieldSegment F hU hF g h t (hseg t ht)
  have hcont : ContinuousOn (fun t => fderiv ℝ F (fieldSegment g h t) h) (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    exact fun t ht => (hasDerivAt_first_dir F hU hF g h t (hseg t ht)).continuousAt.continuousWithinAt
  simpa only [fieldSegment, zero_smul, add_zero, one_smul] using
    (intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable).symm

/-- The exact integral remainder with weight `1-t`, in the original field variables. -/
theorem linearTaylorRemainder_eq_integral (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U) :
    linearTaylorRemainder F g h =
      ∫ t in (0 : ℝ)..1, (1 - t) • secondFDeriv F (fieldSegment g h t) h h := by
  let Φ (t : ℝ) := F (fieldSegment g h t) + (1 - t) • fderiv ℝ F (fieldSegment g h t) h
  have hD : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt Φ
      ((1 - t) • secondFDeriv F (fieldSegment g h t) h h) t := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have hw : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) |>.congr_deriv (by simp)
    have h := (hasDerivAt_comp_fieldSegment F hU hF g h t (hseg t ht)).add
      (hw.smul (hasDerivAt_first_dir F hU hF g h t (hseg t ht)))
    convert h using 1
    simp only [neg_one_smul]
    abel
  have hcont : ContinuousOn (fun t => (1 - t) • secondFDeriv F (fieldSegment g h t) h h)
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    apply (continuous_const.sub continuous_id).continuousOn.smul
    exact fun t ht => (hasDerivAt_second_dir F hU hF g h t (hseg t ht)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable]
  simp only [Φ, fieldSegment, zero_smul, add_zero, sub_zero, one_smul, sub_self, linearTaylorRemainder]
  abel

/-- The quadratic Taylor remainder has its actual third-order integral weight. -/
theorem quadraticTaylorRemainder_eq_integral (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U) :
    quadraticTaylorRemainder F g h =
      ∫ t in (0 : ℝ)..1, ((1 - t)^2 / 2) • thirdFDeriv F (fieldSegment g h t) h h h := by
  let Φ (t : ℝ) := F (fieldSegment g h t) + (1 - t) • fderiv ℝ F (fieldSegment g h t) h +
    ((1 - t)^2 / 2) • secondFDeriv F (fieldSegment g h t) h h
  have hD : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt Φ
      (((1 - t)^2 / 2) • thirdFDeriv F (fieldSegment g h t) h h h) t := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    have hw : HasDerivAt (fun s : ℝ => 1 - s) (-1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t) |>.congr_deriv (by simp)
    have hw₂ : HasDerivAt (fun s : ℝ => (1 - s)^2 / 2) (-(1 - t)) t :=
      ((hw.pow 2).div_const 2).congr_deriv (by ring)
    have h := ((hasDerivAt_comp_fieldSegment F hU hF g h t (hseg t ht)).add
      (hw.smul (hasDerivAt_first_dir F hU hF g h t (hseg t ht)))).add
      (hw₂.smul (hasDerivAt_second_dir F hU hF g h t (hseg t ht)))
    convert h using 1
    simp only [neg_smul, one_smul]
    abel
  have hcont : ContinuousOn (fun t => ((1 - t)^2 / 2) • thirdFDeriv F (fieldSegment g h t) h h h)
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    apply (((continuous_const.sub continuous_id).pow 2).div_const 2).continuousOn.smul
    exact fun t ht => (hasDerivAt_third_dir F hU hF g h t (hseg t ht)).continuousAt.continuousWithinAt
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hD hcont.intervalIntegrable]
  simp only [Φ, fieldSegment, zero_smul, add_zero, sub_zero, one_smul, sub_self, zero_pow (by decide : 2 ≠ 0),
    zero_div, one_pow, quadraticTaylorRemainder, linearTaylorRemainder]
  abel

omit [CompleteSpace W] in
private theorem norm_integral_zero_one_le {f : ℝ → W} {C : ℝ}
    (hC : ∀ t ∈ Icc (0 : ℝ) 1, ‖f t‖ ≤ C) :
    ‖∫ t in (0 : ℝ)..1, f t‖ ≤ C := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := f) (a := 0) (b := 1)
    (fun t ht => hC t (by simpa only [uIcc_of_le zero_le_one] using (uIoc_subset_uIcc ht)))
  simpa using h

theorem norm_sub_le_of_first_field_bound (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖fderiv ℝ F (fieldSegment g h t)‖ ≤ M) :
    ‖F (g + h) - F g‖ ≤ M * ‖h‖ := by
  rw [sub_eq_integral_first_dir F hU hF g h hseg]
  exact norm_integral_zero_one_le fun t ht =>
    (ContinuousLinearMap.le_opNorm _ h).trans (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _))

theorem norm_linearTaylorRemainder_le (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1, ‖secondFDeriv F (fieldSegment g h t)‖ ≤ M) :
    ‖linearTaylorRemainder F g h‖ ≤ M * ‖h‖^2 := by
  rw [linearTaylorRemainder_eq_integral F hU hF g h hseg]
  apply norm_integral_zero_one_le
  intro t ht
  have h₂ : ‖secondFDeriv F (fieldSegment g h t) h h‖ ≤ M * ‖h‖^2 := by
    calc
      _ ≤ ‖secondFDeriv F (fieldSegment g h t) h‖ * ‖h‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖secondFDeriv F (fieldSegment g h t)‖ * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.le_opNorm _ _) (norm_nonneg _)
      _ ≤ (M * ‖h‖) * ‖h‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hM t ht) (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by ring
  have hw : ‖1 - t‖ ≤ (1 : ℝ) := by rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]
  simpa only [norm_smul, one_mul] using mul_le_mul hw h₂ (norm_nonneg _) zero_le_one

theorem norm_quadraticTaylorRemainder_le (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖thirdFDeriv F (fieldSegment g h t) h h h‖ ≤ M * ‖h‖^3) :
    ‖quadraticTaylorRemainder F g h‖ ≤ M * ‖h‖^3 := by
  rw [quadraticTaylorRemainder_eq_integral F hU hF g h hseg]
  apply norm_integral_zero_one_le
  intro t ht
  have hw : ‖(1 - t)^2 / 2‖ ≤ (1 : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg _) (by norm_num))]
    nlinarith [ht.1, ht.2, mul_nonneg ht.1 (sub_nonneg.mpr ht.2)]
  simpa only [norm_smul, one_mul] using mul_le_mul hw (hM t ht) (norm_nonneg _) zero_le_one

theorem norm_linearTaylorRemainder_fderiv_apply_le (F : V → W) {U : Set V}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (g h v : V)
    (hseg : ∀ t ∈ Icc (0 : ℝ) 1, fieldSegment g h t ∈ U)
    {M : ℝ} (hM : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖thirdFDeriv F (fieldSegment g h t) h h v‖ ≤ M * ‖h‖^2 * ‖v‖) :
    ‖linearTaylorRemainder (fderiv ℝ F) g h v‖ ≤ M * ‖h‖^2 * ‖v‖ := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by simp)
  rw [linearTaylorRemainder_eq_integral (fderiv ℝ F) hU hD g h hseg]
  have hcont : ContinuousOn (fun t => (1 - t) • thirdFDeriv F (fieldSegment g h t) h h)
      (uIcc (0 : ℝ) 1) := by
    rw [uIcc_of_le zero_le_one]
    apply (continuous_const.sub continuous_id).continuousOn.smul
    exact fun t ht => (hasDerivAt_second_dir (fderiv ℝ F) hU hD g h t
      (hseg t ht)).continuousAt.continuousWithinAt
  change ‖(ContinuousLinearMap.apply ℝ W v)
      (∫ t in (0 : ℝ)..1, (1 - t) • thirdFDeriv F (fieldSegment g h t) h h)‖ ≤ _
  rw [← (ContinuousLinearMap.apply ℝ W v).intervalIntegral_comp_comm hcont.intervalIntegrable]
  apply norm_integral_zero_one_le
  intro t ht
  have hw : ‖1 - t‖ ≤ (1 : ℝ) := by rw [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr ht.2)]; linarith [ht.1]
  simpa only [ContinuousLinearMap.apply_apply, ContinuousLinearMap.smul_apply, norm_smul, one_mul] using
    mul_le_mul hw (hM t ht) (norm_nonneg _) zero_le_one

end Burnett.V03
