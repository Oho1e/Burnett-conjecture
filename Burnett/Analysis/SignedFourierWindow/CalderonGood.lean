import Burnett.Analysis.SignedFourierWindow.CalderonBlock

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set Function Filter
open scoped ENNReal

def goodPart {ι : Type*} (f : Space → ℂ) (Q : ι → Set Space) (x : Space) : ℂ := by
  classical
  exact if hx : ∃ i, x ∈ Q i then ⨍ y in Q (Classical.choose hx), f y else f x

private theorem good_on {ι : Type*} (f : Space → ℂ) (Q : ι → Set Space)
    (hd : Pairwise (Disjoint on Q)) (i : ι) {x : Space} (hx : x ∈ Q i) :
    goodPart f Q x = ⨍ y in Q i, f y := by
  classical
  have ex : ∃ j, x ∈ Q j := ⟨i,hx⟩
  rw [goodPart,dif_pos ex]
  have hi : Classical.choose ex = i := by
    by_contra hn
    exact disjoint_left.mp (hd hn) (Classical.choose_spec ex) hx
  rw [hi]

private theorem good_out {ι : Type*} (f : Space → ℂ) (Q : ι → Set Space) {x : Space} (hx : x ∉ ⋃ i, Q i) :
    goodPart f Q x = f x := by
  classical
  exact dif_neg (fun h => hx (mem_iUnion.mpr h))

theorem goodPart_measurable {ι : Type*} [Countable ι] (f : Space → ℂ) (hf : Measurable f)
    (Q : ι → Set Space) (hm : ∀ i, MeasurableSet (Q i)) (hd : Pairwise (Disjoint on Q)) :
    Measurable (goodPart f Q) := by
  classical
  intro S hS
  have eq : (goodPart f Q) ⁻¹' S =
      (((⋃ i,Q i)ᶜ ∩ f ⁻¹' S) ∪ ⋃ i, if (⨍ y in Q i,f y) ∈ S then Q i else ∅) := by
    ext x
    by_cases hx : x ∈ ⋃ i,Q i
    · obtain ⟨j,hj⟩ := mem_iUnion.mp hx
      rw [mem_preimage,good_on f Q hd j hj]
      constructor
      · intro h
        exact Or.inr (mem_iUnion.mpr ⟨j,by simpa [h] using hj⟩)
      · rintro (h|h)
        · exact (h.1 hx).elim
        · obtain ⟨i,hi⟩ := mem_iUnion.mp h
          split_ifs at hi with h
          · have e : i=j := by by_contra hn; exact disjoint_left.mp (hd hn) hi hj
            simpa [e] using h
          · exact hi.elim
    · rw [mem_preimage,good_out f Q hx]
      constructor
      · exact fun h => Or.inl ⟨hx,h⟩
      · rintro (h|h)
        · exact h.2
        · obtain ⟨i,hi⟩ := mem_iUnion.mp h
          split_ifs at hi
          · exact (hx (mem_iUnion.mpr ⟨i,hi⟩)).elim
          · exact hi.elim
  rw [eq]
  refine ((MeasurableSet.iUnion hm).compl.inter (hf hS)).union (MeasurableSet.iUnion fun i => ?_)
  split_ifs <;> simp [hm]

theorem good_add_bad {ι : Type*} (f : Space → ℂ) (Q : ι → Set Space)
    (hd : Pairwise (Disjoint on Q)) (x : Space) :
    goodPart f Q x + ∑' i, badBlock f (Q i) x = f x := by
  classical
  by_cases hx : x ∈ ⋃ i,Q i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hx
    rw [tsum_eq_single i,good_on f Q hd i hi,badBlock,indicator_of_mem hi]
    · abel
    · intro j hj
      exact indicator_of_notMem (fun h => disjoint_left.mp (hd hj) h hi) _
  · have zero (i : ι) : badBlock f (Q i) x = 0 := by
      unfold badBlock
      exact indicator_of_notMem (fun h => hx (mem_iUnion.mpr ⟨i,h⟩)) _
    simp only [good_out f Q hx,zero,tsum_zero,add_zero]

theorem good_ae_bound {ι : Type*} (f : Space → ℂ) (hf : Integrable f) (Q : ι → Set Space)
    (hd : Pairwise (Disjoint on Q)) (a : ℝ≥0∞)
    (cover : {x | a < centeredMax (fun y => ‖f y‖ₑ) x} ⊆ ⋃ i,Q i)
    (mean : ∀ i, ‖⨍ y in Q i,f y‖ₑ ≤ a*256) : ∀ᵐ x ∂volume, ‖goodPart f Q x‖ₑ ≤ a*256 := by
  filter_upwards [ae_enorm_le_centeredMax f hf] with x hx
  by_cases hit : x ∈ ⋃ i,Q i
  · obtain ⟨i,hi⟩ := mem_iUnion.mp hit
    rw [good_on f Q hd i hi]
    exact mean i
  · rw [good_out f Q hit]
    exact hx.trans ((le_of_not_gt fun h => hit (cover h)).trans (le_mul_of_one_le_right (zero_le a) (by norm_num)))

end Burnett.Analysis.SignedFourierWindow
