import Mathlib.MeasureTheory.VectorMeasure.Basic

set_option autoImplicit false

noncomputable section
namespace Burnett.Geometry.MeasureGluing

open MeasureTheory Set
open scoped Function

variable {X E : Type*} [MeasurableSpace X] [AddCommMonoid E] [TopologicalSpace E] [T2Space E]

private theorem vectorMeasure_restrict_natUnion_eq
    (v w : VectorMeasure X E) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (h : ∀ n, v.restrict (U n) = w.restrict (U n)) :
    v.restrict (⋃ n, U n) = w.restrict (⋃ n, U n) := by
  ext S hS
  rw [v.restrict_apply (MeasurableSet.iUnion hU) hS, w.restrict_apply (MeasurableSet.iUnion hU) hS]
  let D (n : ℕ) := S ∩ disjointed U n
  have hD (n : ℕ) : MeasurableSet (D n) := hS.inter (MeasurableSet.disjointed hU n)
  have hDis : Pairwise (Disjoint on D) :=
    (disjoint_disjointed U).mono (fun _ _ => Disjoint.mono inf_le_right inf_le_right)
  have hUnion : ⋃ n, D n = S ∩ ⋃ n, U n := by
    change ⋃ n, S ∩ disjointed U n = _
    rw [← inter_iUnion, iUnion_disjointed]
  rw [← hUnion, v.of_disjoint_iUnion hD hDis, w.of_disjoint_iUnion hD hDis]
  apply tsum_congr
  intro n
  have hsub : D n ⊆ U n := inter_subset_right.trans (disjointed_subset U n)
  rw [← v.restrict_eq_self (hU n) (hD n) hsub, h n, w.restrict_eq_self (hU n) (hD n) hsub]

/-- Agreement on a countable measurable cover gives agreement on the full
union. The proof uses countable additivity of the vector measure. -/
theorem vectorMeasure_restrict_iUnion_eq_of_restrict_eq {ι : Type*} [Countable ι]
    (v w : VectorMeasure X E) (U : ι → Set X) (hU : ∀ i, MeasurableSet (U i))
    (h : ∀ i, v.restrict (U i) = w.restrict (U i)) :
    v.restrict (⋃ i, U i) = w.restrict (⋃ i, U i) := by
  cases isEmpty_or_nonempty ι with
  | inl hEmpty =>
    letI : IsEmpty ι := hEmpty
    simp
  | inr hNonempty =>
    letI : Nonempty ι := hNonempty
    obtain ⟨f, hf⟩ := exists_surjective_nat ι
    rw [← hf.iUnion_comp U]
    exact vectorMeasure_restrict_natUnion_eq v w (U ∘ f) (fun n => hU (f n)) (fun n => h (f n))

end Burnett.Geometry.MeasureGluing
