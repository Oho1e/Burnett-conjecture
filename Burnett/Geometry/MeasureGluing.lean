import Mathlib.MeasureTheory.Measure.Restrict

noncomputable section
namespace Burnett.Geometry.MeasureGluing
open MeasureTheory Set

variable {X : Type*} [MeasurableSpace X]

/-- A genuine countable sum of the local measures on disjoint covering pieces. -/
def glued (U : ℕ → Set X) (ν : ℕ → Measure X) : Measure X :=
  Measure.sum (fun n => (ν n).restrict (disjointed U n))

/-- An additional local measure compatible with all cover members is recovered
on its own measurable domain, even if it is not one of the chosen cover charts. -/
theorem glued_restrict_of_compatible
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = univ)
    (ν : ℕ → Measure X) (V : Set X) (hV : MeasurableSet V) (ρ : Measure X)
    (hcompat : ∀ n, (ν n).restrict (U n ∩ V) = ρ.restrict (U n ∩ V)) :
    (glued U ν).restrict V = ρ.restrict V := by
  have hp (n : ℕ) : ((ν n).restrict (disjointed U n)).restrict V =
      (ρ.restrict V).restrict (disjointed U n) := by
    rw [Measure.restrict_restrict hV, Measure.restrict_restrict (MeasurableSet.disjointed hU n)]
    have hsub : V ∩ disjointed U n ⊆ U n ∩ V :=
      fun x hx => ⟨disjointed_subset U n hx.2, hx.1⟩
    have hh := congrArg (fun μ : Measure X => μ.restrict (V ∩ disjointed U n)) (hcompat n)
    dsimp only at hh
    rw [Measure.restrict_restrict_of_subset hsub,
      Measure.restrict_restrict_of_subset hsub] at hh
    simpa only [inter_comm] using hh
  unfold glued
  rw [Measure.restrict_sum_of_countable]
  calc
    Measure.sum (fun n => ((ν n).restrict (disjointed U n)).restrict V) =
        Measure.sum (fun n => (ρ.restrict V).restrict (disjointed U n)) :=
      congrArg Measure.sum (funext hp)
    _ = (ρ.restrict V).restrict (⋃ n, disjointed U n) :=
      (Measure.restrict_iUnion (disjoint_disjointed U) (MeasurableSet.disjointed hU)).symm
    _ = ρ.restrict V := by rw [iUnion_disjointed, hcover, Measure.restrict_univ]

theorem glued_restrict
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = univ)
    (ν : ℕ → Measure X)
    (hcompat : ∀ i j, (ν i).restrict (U i ∩ U j) = (ν j).restrict (U i ∩ U j))
    (i : ℕ) : (glued U ν).restrict (U i) = (ν i).restrict (U i) :=
  glued_restrict_of_compatible U hU hcover ν (U i) (hU i) (ν i) (fun n => hcompat n i)

theorem eq_glued_of_restrict
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = univ)
    (ν : ℕ → Measure X)
    (hcompat : ∀ i j, (ν i).restrict (U i ∩ U j) = (ν j).restrict (U i ∩ U j))
    (μ : Measure X) (hμ : ∀ i, μ.restrict (U i) = (ν i).restrict (U i)) : μ = glued U ν :=
  Measure.ext_of_iUnion_eq_univ hcover
    (fun i => (hμ i).trans (glued_restrict U hU hcover ν hcompat i).symm)

theorem existsUnique_measure_of_compatible_cover
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (hcover : ⋃ n, U n = univ)
    (ν : ℕ → Measure X)
    (hcompat : ∀ i j, (ν i).restrict (U i ∩ U j) = (ν j).restrict (U i ∩ U j)) :
    ∃! μ : Measure X, ∀ i, μ.restrict (U i) = (ν i).restrict (U i) :=
  ⟨glued U ν, glued_restrict U hU hcover ν hcompat,
    fun μ hμ => eq_glued_of_restrict U hU hcover ν hcompat μ hμ⟩

end Burnett.Geometry.MeasureGluing
