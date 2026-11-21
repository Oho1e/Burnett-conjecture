import Burnett.Analysis.AngularCaps.ProjectiveNullGeometry

set_option autoImplicit false
set_option maxHeartbeats 3800000
noncomputable section

namespace Burnett.Analysis.ProjectiveNullCaps

open Finset Set Metric
open scoped BigOperators

/-- Greedy extraction of a projectively separated subcover of a finite set. -/
theorem exists_projectiveSeparated_subcover (s : Finset Vec) {r : ℝ} (hr : 0 ≤ r) :
    ∃ t : Finset Vec, t ⊆ s ∧
      (↑t : Set Vec).Pairwise (fun x y => r < projectiveDist x y) ∧
      ∀ x ∈ s, ∃ y ∈ t, projectiveDist x y ≤ r := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ⟨∅, by simp, by simp, by simp⟩
  | @insert z s hz ih =>
    obtain ⟨t, hts, hSep, hCover⟩ := ih
    by_cases hNear : ∃ y ∈ t, projectiveDist z y ≤ r
    · refine ⟨t, fun x hx => Finset.mem_insert_of_mem (hts hx), hSep, fun x hx => ?_⟩
      rcases Finset.mem_insert.mp hx with h | h
      · exact h ▸ hNear
      · exact hCover x h
    · have hzFar (y : Vec) (hy : y ∈ t) : r < projectiveDist z y :=
        lt_of_not_ge (fun h => hNear ⟨y,hy,h⟩)
      refine ⟨insert z t, Finset.insert_subset_insert _ hts, ?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_insert.mp hx with h | h
        · subst x
          rcases Finset.mem_insert.mp hy with h | h
          · exact (hxy h.symm).elim
          · exact hzFar y h
        · rcases Finset.mem_insert.mp hy with h' | h'
          · rw [h', projectiveDist_comm]
            exact hzFar x h
          · exact hSep h h' hxy
      · intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · subst x
          exact ⟨z, Finset.mem_insert_self _ _, by simpa only [projectiveDist_self] using hr⟩
        · obtain ⟨y,hy,hD⟩ := hCover x h
          exact ⟨y, Finset.mem_insert_of_mem hy, hD⟩

theorem projective_openCap_eq_signed_balls (w : Vec) (r : ℝ) :
    {v : Vec | projectiveDist v w < r} = ball w r ∪ ball (-w) r := by
  ext v
  simp only [Set.mem_setOf_eq, Set.mem_union, projectiveDist, Metric.mem_ball, dist_eq_norm,
    sub_neg_eq_add, min_lt_iff]

theorem unitNull_closed_under_sign {m : Form} {v : Vec} (hv : v ∈ unitNull m) : -v ∈ unitNull m := by
  constructor
  · simpa only [norm_neg] using hv.1
  · rw [← neg_one_smul ℝ v, quadratic_smul, hv.2, mul_zero]

end Burnett.Analysis.ProjectiveNullCaps
