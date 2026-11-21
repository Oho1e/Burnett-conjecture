import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.Preorder.Finite

set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Set MeasureTheory
open scoped BigOperators ENNReal Classical

variable {X ι : Type*}

/-- Every element of a finite family lies inside one of the maximal elements
of the same family, ordered by containment. -/
theorem finite_maximal_set_cover (J : Finset ι) (Q : ι → Set X) (i : ι) (hi : i ∈ J) :
    ∃ j ∈ J, Q i ⊆ Q j ∧ ∀ k ∈ J, Q j ⊆ Q k → Q k ⊆ Q j := by
  classical
  let W := J.filter (fun j => Q i ⊆ Q j)
  have hW : W.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨hi,subset_rfl⟩⟩
  obtain ⟨j,hj⟩ := W.exists_maximalFor Q hW
  have hj' : j ∈ J ∧ Q i ⊆ Q j := Finset.mem_filter.mp hj.1
  refine ⟨j,hj'.1,hj'.2,fun k hk hIncl => ?_⟩
  exact hj.2 (Finset.mem_filter.mpr ⟨hk,hj'.2.trans hIncl⟩) hIncl

variable [MeasurableSpace X]

/-- The finite packing condition gives the distribution bound for any
nonnegative weight on a nested-or-disjoint family of measurable sets. -/
theorem finite_packing_level_le (μ : Measure X) (I : Finset ι) (Q : ι → Set X)
    (mQ : ∀ i ∈ I, MeasurableSet (Q i))
    (hinj : ∀ i ∈ I, ∀ j ∈ I, Q i = Q j → i = j)
    (nested : ∀ i ∈ I, ∀ j ∈ I, Q i ⊆ Q j ∨ Q j ⊆ Q i ∨ Disjoint (Q i) (Q j))
    (w : ι → ℝ≥0∞) (C : ℝ≥0∞)
    (pack : ∀ j ∈ I, (∑ i ∈ I.filter (fun i => Q i ⊆ Q j), w i) ≤ C*μ (Q j))
    (a : ι → ℝ) (F : X → ℝ) (dom : ∀ i ∈ I, ∀ x ∈ Q i, a i ≤ F x) (t : ℝ) :
    (∑ i ∈ I.filter (fun i => t < a i), w i) ≤ C*μ {x | t < F x} := by
  classical
  let J := I.filter (fun i => t < a i)
  let M := J.filter (fun j => ∀ k ∈ J, Q j ⊆ Q k → Q k ⊆ Q j)
  have hJ : J ⊆ I := Finset.filter_subset _ _
  have hM (j : ι) (hj : j ∈ M) : j ∈ J ∧ ∀ k ∈ J, Q j ⊆ Q k → Q k ⊆ Q j :=
    Finset.mem_filter.mp hj
  have hPair : Set.PairwiseDisjoint (↑M : Set ι) Q := by
    intro i hi j hj hij
    obtain h | h | h := nested i (hJ (hM i hi).1) j (hJ (hM j hj).1)
    · exact (hij (hinj i (hJ (hM i hi).1) j (hJ (hM j hj).1)
        (Subset.antisymm h ((hM i hi).2 j (hM j hj).1 h)))).elim
    · exact (hij (hinj i (hJ (hM i hi).1) j (hJ (hM j hj).1)
        (Subset.antisymm ((hM j hj).2 i (hM i hi).1 h) h))).elim
    · exact h
  let A (i j : ι) := if Q i ⊆ Q j then w i else 0
  have hCover (i : ι) (hi : i ∈ J) : w i ≤ ∑ j ∈ M, A i j := by
    obtain ⟨j,hj,hIncl,hMax⟩ := finite_maximal_set_cover J Q i hi
    have hjm : j ∈ M := Finset.mem_filter.mpr ⟨hj,hMax⟩
    have hA : A i j = w i := if_pos hIncl
    rw [← hA]
    exact Finset.single_le_sum (fun _ _ => zero_le _) hjm
  have hIntegrate (j : ι) (hj : j ∈ M) : (∑ i ∈ J, A i j) ≤ C*μ (Q j) := by
    have hPack := pack j (hJ (hM j hj).1)
    rw [Finset.sum_filter] at hPack
    exact (Finset.sum_le_sum_of_subset hJ).trans hPack
  have hU : (⋃ j ∈ M, Q j) ⊆ {x | t < F x} := by
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨j,hj,hx⟩ := hx
    have h := Finset.mem_filter.mp (hM j hj).1
    exact h.2.trans_le (dom j h.1 x hx)
  change (∑ i ∈ J, w i) ≤ _
  calc
    _ ≤ ∑ i ∈ J, ∑ j ∈ M, A i j := Finset.sum_le_sum hCover
    _ = ∑ j ∈ M, ∑ i ∈ J, A i j := Finset.sum_comm
    _ ≤ ∑ j ∈ M, C*μ (Q j) := Finset.sum_le_sum hIntegrate
    _ = C*μ (⋃ j ∈ M, Q j) := by
      rw [measure_biUnion_finset hPair (fun j hj => mQ j (hJ (hM j hj).1)), Finset.mul_sum]
    _ ≤ _ := mul_le_mul_left' (measure_mono hU) C

end Burnett.Analysis.CarlesonEmbedding
