import Burnett.Analysis.SignedFourierWindow.CalderonBalls

set_option autoImplicit false
noncomputable section
namespace Burnett.Analysis.SignedFourierWindow
open Burnett.Analysis.CenteredMaximal hiding Space
local notation "Space" => EuclideanSpace ℝ (Fin 4)
open MeasureTheory Set Metric Function
open scoped ENNReal

/-- Reserve every disjoint inner ball, then assign the other points to the
first enlarged ball containing them in a countable enumeration. -/
private def assigned {ι : Type*} [Encodable ι] (B U : ι → Set Space) (i : ι) : Set Space :=
  B i ∪ ((U i \ ⋃ j, B j) \ ⋃ j, ⋃ (_ : Encodable.encode j < Encodable.encode i), U j)

private theorem measurable_assigned {ι : Type*} [Encodable ι] (B U : ι → Set Space)
    (hmB : ∀ i, MeasurableSet (B i)) (hmU : ∀ i, MeasurableSet (U i)) (i : ι) :
    MeasurableSet (assigned B U i) :=
  (hmB i).union (((hmU i).diff (MeasurableSet.iUnion hmB)).diff
    (MeasurableSet.iUnion fun j => MeasurableSet.iUnion fun _ => hmU j))

private theorem reserved_partition {ι : Type*} [Encodable ι] (B U : ι → Set Space)
    (hd : Pairwise (Disjoint on B)) (sub : ∀ i, B i ⊆ U i) :
    Pairwise (Disjoint on assigned B U) ∧
    (∀ i, B i ⊆ assigned B U i ∧ assigned B U i ⊆ U i) ∧ (⋃ i, assigned B U i) = ⋃ i, U i := by
  classical
  have inside (i : ι) : assigned B U i ⊆ U i :=
    fun _ hx => hx.elim (fun h => sub i h) (fun h => h.1.1)
  refine ⟨?_,fun i => ⟨fun _ h => Or.inl h,inside i⟩,Subset.antisymm (iUnion_mono inside) ?_⟩
  · intro i j hij
    refine disjoint_left.mpr (fun z hi hj => ?_)
    rcases hi with hi|hi <;> rcases hj with hj|hj
    · exact disjoint_left.mp (hd hij) hi hj
    · exact hj.1.2 (mem_iUnion.mpr ⟨i,hi⟩)
    · exact hi.1.2 (mem_iUnion.mpr ⟨j,hj⟩)
    · rcases lt_or_gt_of_ne (fun h => hij (Encodable.encode_injective h)) with h|h
      · exact hj.2 (mem_iUnion₂.mpr ⟨i,h,hi.1.1⟩)
      · exact hi.2 (mem_iUnion₂.mpr ⟨j,h,hj.1.1⟩)
  · intro z hz
    by_cases hB : z ∈ ⋃ j, B j
    · obtain ⟨i,hi⟩ := mem_iUnion.mp hB
      exact mem_iUnion.mpr ⟨i,Or.inl hi⟩
    obtain ⟨j,hj⟩ := mem_iUnion.mp hz
    let P := fun n : ℕ => ∃ i : ι, Encodable.encode i = n ∧ z ∈ U i
    have ex : ∃ n, P n := ⟨_,j,rfl,hj⟩
    obtain ⟨i,hi,hit⟩ := Nat.find_spec ex
    refine mem_iUnion.mpr ⟨i,Or.inr ⟨⟨hit,hB⟩,?_⟩⟩
    intro bad
    obtain ⟨k,hki,hk⟩ := mem_iUnion₂.mp bad
    exact Nat.find_min ex (hki.trans_le hi.le) ⟨k,rfl,hk⟩

/-- Measurable, disjoint Calderón–Zygmund regions at a positive level. Each
piece has an inner ball of high average and lies in its own fourfold ball with
average below the level. The complement is outside the maximal superlevel. -/
theorem calderon_regions (g : Space → ℝ≥0∞) (hg : (∫⁻ y,g y) < ⊤) (a : ℝ≥0∞) (ha : 0<a) :
    ∃ (u : Set Space) (r : Space → ℝ) (Q : u → Set Space), u.Countable ∧ Pairwise (Disjoint on Q) ∧
      (∀ i : u, MeasurableSet (Q i) ∧ 0<r i ∧ closedBall (i:Space) (r i) ⊆ Q i ∧ Q i ⊆ closedBall (i:Space) (4*r i)) ∧
      {x | a < centeredMax g x} ⊆ ⋃ i : u, Q i ∧
      (∀ i : u, a * volume (closedBall (i:Space) (r i)) < ∫⁻ y in closedBall (i:Space) (r i), g y) ∧
      (∀ i : u, (∫⁻ y in Q i, g y) ≤ a * (256*volume (Q i))) := by
  classical
  obtain ⟨u,r,hu,disj,cover,lower,upper⟩ := calderon_ball_selection g hg a ha
  letI : Encodable u := hu.toEncodable
  let B := fun i : u => closedBall (i:Space) (r i)
  let U := fun i : u => closedBall (i:Space) (4*r i)
  have hd : Pairwise (Disjoint on B) := fun i j hij => disj i.2 j.2 (Subtype.coe_injective.ne hij)
  have incl (i : u) : B i ⊆ U i := closedBall_subset_closedBall (by linarith [(lower i i.2).1])
  obtain ⟨hds,hs,he⟩ := reserved_partition B U hd incl
  let Q := assigned B U
  refine ⟨u,r,Q,hu,hds,fun i => ⟨measurable_assigned _ _ (fun _ => measurableSet_closedBall)
    (fun _ => measurableSet_closedBall) i,(lower i i.2).1,(hs i).1,(hs i).2⟩,?_,
    fun i => (lower i i.2).2,?_⟩
  · intro x hx
    rw [show (⋃ i : u,Q i) = ⋃ i : u,U i from he]
    obtain ⟨y,hy,hit⟩ := mem_iUnion₂.mp (cover hx)
    exact mem_iUnion.mpr ⟨⟨y,hy⟩,hit⟩
  · intro i
    have hv : volume (U i) = 256*volume (B i) := by
      dsimp only [U,B]
      rw [Measure.addHaar_closedBall_mul volume (i:Space) (by norm_num : (0:ℝ) ≤ 4) (lower i i.2).1.le,
        Measure.addHaar_closedBall_center volume (i:Space)]
      norm_num [show Module.finrank ℝ Space = 4 from finrank_euclideanSpace_fin]
    apply (lintegral_mono_set (hs i).2).trans
    apply (upper i i.2).trans
    change a * volume (U i) ≤ _
    rw [hv]
    exact mul_le_mul_left' (mul_le_mul_left' (measure_mono (hs i).1) 256) a

end Burnett.Analysis.SignedFourierWindow
