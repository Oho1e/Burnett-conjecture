import Burnett.Geometry.MeasureGluing
import Mathlib.MeasureTheory.Measure.AEMeasurable

set_option autoImplicit false

noncomputable section
namespace Burnett.Geometry.MeasureGluing

open Set MeasureTheory

variable {X : Type*} {F : X → Type*}

private theorem exists_disjointed_window (U : ℕ → Set X) (cover : ⋃ i, U i = univ) (x : X) :
    ∃ i, x ∈ disjointed U i := by
  apply mem_iUnion.mp
  rw [iUnion_disjointed, cover]
  exact mem_univ x

/-- On each disjoint piece of the cover, use its original dependent section. -/
def gluedSection (U : ℕ → Set X) (cover : ⋃ i, U i = univ)
    (J : ℕ → (x : X) → F x) (x : X) : F x :=
  J (exists_disjointed_window U cover x).choose x

theorem gluedSection_eq_of_mem_disjointed (U : ℕ → Set X) (cover : ⋃ i, U i = univ)
    (J : ℕ → (x : X) → F x) {i : ℕ} {x : X} (hx : x ∈ disjointed U i) :
    gluedSection U cover J x = J i x := by
  let n := (exists_disjointed_window U cover x).choose
  have hn : x ∈ disjointed U n := (exists_disjointed_window U cover x).choose_spec
  have heq : n = i := by
    by_contra h
    exact Set.disjoint_left.mp (disjoint_disjointed U h) hn hx
  change J n x = J i x
  rw [heq]

/-- A compatible local section and its control measure are recovered on their
whole measurable window, including windows outside the chosen cover family. -/
theorem gluedMeasureSection_restrict_of_compatible [MeasurableSpace X]
    (U : ℕ → Set X) (hU : ∀ i, MeasurableSet (U i)) (cover : ⋃ i, U i = univ)
    (ν : ℕ → Measure X) (J : ℕ → (x : X) → F x)
    (V : Set X) (hV : MeasurableSet V) (η : Measure X) (A : (x : X) → F x)
    (hMeasure : ∀ i, (ν i).restrict (U i ∩ V) = η.restrict (U i ∩ V))
    (hSection : ∀ i, ∀ᵐ x ∂η.restrict (U i ∩ V), J i x = A x) :
    (glued U ν).restrict V = η.restrict V ∧
      ∀ᵐ x ∂η.restrict V, gluedSection U cover J x = A x := by
  refine ⟨glued_restrict_of_compatible U hU cover ν V hV η hMeasure, ?_⟩
  have hAll : ∀ᵐ x ∂η, ∀ i, x ∈ U i ∩ V → J i x = A x :=
    ae_all_iff.mpr fun i => (ae_restrict_iff' ((hU i).inter hV)).mp (hSection i)
  filter_upwards [ae_restrict_of_ae (s := V) hAll, ae_restrict_mem (μ := η) hV] with x hEq hx
  obtain ⟨i, hi⟩ := exists_disjointed_window U cover x
  exact (gluedSection_eq_of_mem_disjointed U cover J hi).trans
    (hEq i ⟨disjointed_subset U i hi, hx⟩)

end Burnett.Geometry.MeasureGluing
