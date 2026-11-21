import Burnett.Analysis.AngularCaps.ProjectiveSeparated
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
set_option maxHeartbeats 5300000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set Metric MeasureTheory
open scoped BigOperators ENNReal

private abbrev unitVolume : ℝ := (volume : Measure Vec).real (ball (0:Vec) 1)

private theorem unitVolume_pos : 0 < unitVolume :=
  ENNReal.toReal_pos (measure_ball_pos volume _ zero_lt_one).ne' measure_ball_lt_top.ne

private theorem real_ball_volume (v : Vec) (r : ℝ) (hr : 0 ≤ r) :
    (volume : Measure Vec).real (ball v r) = r^4*unitVolume := by
  rw [← Measure.addHaar_real_closedBall_eq_addHaar_real_ball volume v r,
    Measure.addHaar_real_closedBall volume v hr, finrank_euclideanSpace_fin]

/-- A fixed-radius Euclidean packing bound with the exact dimension-four
volume ratio. -/
theorem card_ambientBall_packing_le {ι : Type*} (s : Finset ι) (c : ι → Vec) (v : Vec) {r R : ℝ}
    (hr : 0 < r) (hR : 0 ≤ R) (hNear : ∀ i ∈ s, dist (c i) v ≤ R)
    (hSep : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → 2*r ≤ dist (c i) (c j)) :
    (s.card : ℝ) ≤ ((R+r)/r)^4 := by
  let U (i : ι) := ball (c i) r
  have hDisjoint : PairwiseDisjoint (↑s : Set ι) U := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    intro z hzᵢ hzⱼ
    have hᵢ : dist z (c i) < r := Metric.mem_ball.mp hzᵢ
    have hⱼ : dist z (c j) < r := Metric.mem_ball.mp hzⱼ
    have hT := (hSep i hi j hj hij).trans (dist_triangle (c i) z (c j))
    rw [dist_comm (c i) z] at hT
    linarith only [hT, hᵢ, hⱼ]
  have hSubset : (⋃ i ∈ s, U i) ⊆ ball v (R+r) := by
    intro x hx
    obtain ⟨i, hx'⟩ := Set.mem_iUnion.mp hx
    obtain ⟨hi, hxU⟩ := Set.mem_iUnion.mp hx'
    have h := dist_triangle x (c i) v
    have hXi : dist x (c i) < r := Metric.mem_ball.mp hxU
    exact Metric.mem_ball.mpr (h.trans_lt (by linarith only [hXi, hNear i hi]))
  have hVol : (∑ i ∈ s, (volume : Measure Vec) (U i)) ≤ volume (ball v (R+r)) := by
    rw [← measure_biUnion_finset hDisjoint (fun i _ => measurableSet_ball (x := c i) (ε := r))]
    exact measure_mono hSubset
  have hReal := ENNReal.toReal_mono (measure_ball_lt_top.ne) hVol
  rw [ENNReal.toReal_sum (fun i _ => measure_ball_lt_top.ne)] at hReal
  change (∑ i ∈ s, (volume : Measure Vec).real (ball (c i) r)) ≤
    (volume : Measure Vec).real (ball v (R+r)) at hReal
  simp only [real_ball_volume _ r hr.le, real_ball_volume v (R+r) (add_nonneg hR hr.le)] at hReal
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc] at hReal
  have hCount : (s.card : ℝ)*r^4 ≤ (R+r)^4 := (mul_le_mul_iff_left₀ unitVolume_pos).mp hReal
  rw [div_pow]
  exact (le_div_iff₀ (pow_pos hr _)).mpr hCount

end Burnett.Analysis.ProjectiveNullCaps
