import Burnett.Analysis.AllScaleTransfer.ActualNearAngularSum
import Burnett.Analysis.AllScaleTransfer.ActualFiniteCapTailFactors

set_option autoImplicit false
set_option maxHeartbeats 5500000

noncomputable section

namespace Burnett.Analysis.CapFourier
open Burnett.Analysis.CenteredMaximal hiding Space
open Burnett.Analysis.DyadicSquare hiding Space

open Set MeasureTheory
open Burnett.Analysis.ProjectiveNullCaps
open Burnett.A02.FrequencySplit
open Burnett.A05 (triLpMass_pullbackTrilinearFactor_L3_cancel)
open scoped ENNReal

local instance : Fact (1 ≤ ENNReal.ofReal (3 : ℝ)) := ⟨by norm_num⟩

private theorem original_bound_of_normalized (A : Space ≃L[ℝ] Space)
    (m : Joint → ℂ) (f g h : SchwartzMap Space ℂ) (B : ℝ)
    (hB : ‖radianTrilinearForm (m ∘ pairedFrequencyEquiv A)
        (pullbackTrilinearFactor A f) (pullbackTrilinearFactor A g) (pullbackTrilinearFactor A h)‖ ≤
      B * (triLpMass (pullbackTrilinearFactor A f) (pullbackTrilinearFactor A g)
        (pullbackTrilinearFactor A h) 3 3 3).toReal) :
    ‖radianTrilinearForm m f g h‖ ≤
      B * (‖f.toLp (ENNReal.ofReal 3) volume‖ * ‖g.toLp (ENNReal.ofReal 3) volume‖ *
        ‖h.toLp (ENNReal.ofReal 3) volume‖) := by
  have hJ : 0 ≤ (linearJacobian A)⁻¹ := inv_nonneg.mpr (linearJacobian_pos A).le
  rw [radianTrilinearForm_pairedFrequency A, norm_smul, Real.norm_of_nonneg hJ]
  refine (mul_le_mul_of_nonneg_left hB hJ).trans_eq ?_
  rw [mul_left_comm,triLpMass_pullbackTrilinearFactor_L3_cancel]
  simp only [triLpMass,ENNReal.toReal_mul,SchwartzMap.toLp,Lp.norm_toLp]

/-- The paired-frequency change and cap Hölder step apply to the actual
finite contractions of the three projected fields. The normalized
coefficient estimates enter on the same cap chart and factors. -/
theorem radian_near_field_bound_of_normalized_bounds
    {ι χ : Type*} [Fintype ι] [Fintype χ]
    {metric : Form} {δ η inner outer enlarged D C₃ : ℝ}
    (S : SmoothThinConeCaps metric δ η inner outer enlarged D)
    (Pplus : ∀ j : ↑S.centers, CapLpRealization (ENNReal.ofReal 3)
      (enlargedCapMultiplier metric δ η outer enlarged j) C₃)
    {q Cκ A C : ℝ} (hq : 3 < q) (hδ : δ ∈ Ioc (0 : ℝ) 1)
    (hD : 0 < D) (hCκ : 0 ≤ Cκ) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hAngular : ∀ v : FieldLp ι (ENNReal.ofReal 3),
      (∑ j : ↑S.centers, ‖(Pplus j).fieldAction v‖^3)^(1/3 : ℝ) ≤
        ((Fintype.card ι : ℝ) * C) * (S.centers.card : ℝ)^(1/(3*(q-2))) * ‖v‖)
    (f g h : FieldLp ι (ENNReal.ofReal 3))
    (F G W : ↑S.centers → ι → SchwartzMap Space ℂ)
    (hF : ∀ j i, (F j i).toLp (ENNReal.ofReal 3) volume = fieldCoordinateLp i ((Pplus j).fieldAction f))
    (hG : ∀ j i, (G j i).toLp (ENNReal.ofReal 3) volume = fieldCoordinateLp i ((Pplus j).fieldAction g))
    (hW : ∀ j i, (W j i).toLp (ENNReal.ofReal 3) volume = fieldCoordinateLp i ((Pplus j).fieldAction h))
    (left middle right : χ → ι) (m : ↑S.centers → χ → Joint → ℂ)
    (chart : ∀ j : ↑S.centers, NullCapChart metric j) :
    let dil (j : ↑S.centers) := capFrequencyEquiv (chart j) hδ.1.ne'
    (∀ j k,
      let f' := pullbackTrilinearFactor (dil j) (F j (left k))
      let g' := pullbackTrilinearFactor (dil j) (G j (middle k))
      let h' := pullbackTrilinearFactor (dil j) (W j (right k))
      ‖radianTrilinearForm (m j k ∘ pairedFrequencyEquiv (dil j)) f' g' h'‖ ≤
        (Cκ * A * δ^2) * (triLpMass f' g' h' 3 3 3).toReal) →
    ‖∑ j : ↑S.centers, ∑ k : χ, radianTrilinearForm (m j k) (F j (left k)) (G j (middle k)) (W j (right k))‖ ≤
      ((Cκ * (Fintype.card χ : ℝ)) * ((Fintype.card ι : ℝ) * C)^3 * D^(1/(q-2))) *
        A * δ^(2*(q-3)/(q-2)) * ‖f‖ * ‖g‖ * ‖h‖ := by
  intro dil hNorm
  let T (j : ↑S.centers) (k : χ) := radianTrilinearForm (m j k) (F j (left k)) (G j (middle k)) (W j (right k))
  let X (v : FieldLp ι (ENNReal.ofReal 3)) (j : ↑S.centers) := ‖(Pplus j).fieldAction v‖
  let SumCap (j : ↑S.centers) (_f _g _h : FieldLp ι (ENNReal.ofReal 3)) := ∑ k : χ, T j k
  have hTerm (j : ↑S.centers) (k : χ) : ‖T j k‖ ≤ Cκ * A * δ^2 * (X f j * X g j * X h j) := by
    have e := original_bound_of_normalized (dil j) (m j k) (F j (left k)) (G j (middle k)) (W j (right k))
      (Cκ * A * δ^2) (hNorm j k)
    have bF : ‖(F j (left k)).toLp (ENNReal.ofReal 3) volume‖ ≤ X f j := by
      rw [hF]
      exact fieldCoordinateLp_norm_le _ _
    have bG : ‖(G j (middle k)).toLp (ENNReal.ofReal 3) volume‖ ≤ X g j := by
      rw [hG]
      exact fieldCoordinateLp_norm_le _ _
    have bW : ‖(W j (right k)).toLp (ENNReal.ofReal 3) volume‖ ≤ X h j := by
      rw [hW]
      exact fieldCoordinateLp_norm_le _ _
    refine e.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact mul_le_mul (mul_le_mul bF bG (norm_nonneg _) (norm_nonneg _)) bW (norm_nonneg _) (by unfold X; positivity)
  have hCap (j : ↑S.centers) :
      ‖SumCap j f g h‖ ≤ (Cκ * (Fintype.card χ : ℝ)) * A * δ^2 * (X f j * X g j * X h j) := by
    calc
      _ ≤ ∑ k : χ, ‖T j k‖ := norm_sum_le _ _
      _ ≤ ∑ _k : χ, Cκ * A * δ^2 * (X f j * X g j * X h j) :=
        Finset.sum_le_sum (fun k _ => hTerm j k)
      _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring
  exact actual_near_angular_sum_bound S Pplus hq hδ hD (mul_nonneg hCκ (Nat.cast_nonneg _))
    hA hC hAngular SumCap f g h hCap

end Burnett.Analysis.CapFourier
