import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.CenteredMaximal

abbrev Space := EuclideanSpace ℝ (Fin 4)

open MeasureTheory Set Metric
open scoped ENNReal BigOperators

/-- A witness ball has average strictly above the threshold. The product form
avoids division at zero or infinity. -/
def ballLevel (g : Space → ℝ≥0∞) (level : ℝ≥0∞) (R : ℝ) : Set Space :=
  {x | ∃ r : ℝ, 0<r ∧ r ≤ R ∧ level*volume (closedBall x r) < ∫⁻ y in closedBall x r, g y}

theorem ballLevel_weak_one (g : Space → ℝ≥0∞) (level : ℝ≥0∞) (R : ℝ) :
    level * volume (ballLevel g level R) ≤ 256 * ∫⁻ x, g x := by
  classical
  let T := ballLevel g level R
  choose! rad hr using (show ∀ x ∈ T, ∃ r : ℝ, 0<r ∧ r ≤ R ∧
      level*volume (closedBall x r) < ∫⁻ y in closedBall x r, g y from fun _ h => h)
  obtain ⟨u,hsub,hd,hcover⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    T id rad R (fun x hx => (hr x hx).2.1) 4 (by norm_num)
  change u.PairwiseDisjoint (fun x => closedBall x (rad x)) at hd
  have ho : u.PairwiseDisjoint (fun x => ball x (rad x)) := by
    intro x hx y hy hxy
    exact (hd hx hy hxy).mono ball_subset_closedBall ball_subset_closedBall
  have hu : u.Countable := ho.countable_of_isOpen (fun _ _ => isOpen_ball)
    (fun x hx => ⟨x,mem_ball_self (hr x (hsub hx)).1⟩)
  have cover : T ⊆ ⋃ y ∈ u, closedBall y (4*rad y) := by
    intro x hx
    obtain ⟨y,hy,hs⟩ := hcover x hx
    exact mem_iUnion₂.mpr ⟨y,hy,hs (mem_closedBall_self (hr x hx).1.le)⟩
  have volume4 (x : u) : volume (closedBall (x:Space) (4*rad x)) = 256*volume (closedBall (x:Space) (rad x)) := by
    rw [Measure.addHaar_closedBall_mul volume (x:Space) (by norm_num : (0:ℝ) ≤ 4) (hr x (hsub x.2)).1.le,
      Measure.addHaar_closedBall_center volume (x:Space)]
    norm_num [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]
  calc
    _ ≤ level * ∑' y : u, volume (closedBall (y:Space) (4*rad y)) :=
      mul_le_mul_left' ((measure_mono cover).trans (measure_biUnion_le volume hu _)) _
    _ = 256 * ∑' y : u, level * volume (closedBall (y:Space) (rad y)) := by
      simp_rw [volume4,ENNReal.tsum_mul_left]
      ac_rfl
    _ ≤ 256 * ∑' y : u, ∫⁻ x in closedBall (y:Space) (rad y), g x := by
      apply mul_le_mul_left'
      exact ENNReal.tsum_le_tsum (fun y => (hr y (hsub y.2)).2.2.le)
    _ ≤ _ := by
      rw [← lintegral_biUnion (μ := volume) hu (fun _ _ => measurableSet_closedBall) hd g]
      exact mul_le_mul_left' (setLIntegral_le_lintegral _ _) _

/-- Uniform weak (1,1) estimate on the full centered Hardy–Littlewood
superlevel set, allowing every positive real radius on four-dimensional space. -/
theorem centered_maximal_weak_one (g : Space → ℝ≥0∞) (level : ℝ≥0∞) :
    level * volume {x | ∃ r : ℝ, 0<r ∧ level*volume (closedBall x r) < ∫⁻ y in closedBall x r, g y} ≤
      256 * ∫⁻ y, g y := by
  let A := fun N : ℕ => ballLevel g level N
  have ha : Monotone A := by
    intro n m h x hx
    obtain ⟨r,hr,hrn,hi⟩ := hx
    exact ⟨r,hr,hrn.trans (by exact_mod_cast h),hi⟩
  have eqlevel : {x | ∃ r : ℝ, 0<r ∧ level*volume (closedBall x r) < ∫⁻ y in closedBall x r, g y} = ⋃ n, A n := by
    ext x
    constructor
    · rintro ⟨r,hr,hi⟩
      obtain ⟨n,hn⟩ := exists_nat_ge r
      exact mem_iUnion.mpr ⟨n,r,hr,hn,hi⟩
    · intro h
      obtain ⟨n,r,hr,_,hi⟩ := mem_iUnion.mp h
      exact ⟨r,hr,hi⟩
  rw [eqlevel,ha.measure_iUnion,ENNReal.mul_iSup]
  exact iSup_le (fun n => ballLevel_weak_one g level n)

end Burnett.Analysis.CenteredMaximal
