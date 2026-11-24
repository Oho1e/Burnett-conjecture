import Burnett.Geometry.MeasureGluing
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Compactness.Compact

set_option autoImplicit false

noncomputable section
namespace Burnett.Geometry.MeasureGluing

open Set MeasureTheory
open scoped Topology ENNReal

variable {X M : Type*} [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace M]

/-- Compact-base finiteness of compatible chart controls. Open windows lying
inside the measurable gluing windows give finite subcovers of compact bases. -/
theorem glued_locallyFinite_and_finiteOnCompactBase
    (π : X → M) (hπ : Continuous π) (W V : ℕ → Set M)
    (hW : ∀ i, MeasurableSet (π ⁻¹' W i)) (hV : ∀ i, IsOpen (V i))
    (cover : ⋃ i, V i = univ) (hSub : ∀ i, V i ⊆ W i)
    (τ : ℕ → Measure X) (hFinite : ∀ i, τ i (π ⁻¹' W i) < ⊤)
    (hCompat : ∀ i j, (τ i).restrict (π ⁻¹' W i ∩ π ⁻¹' W j) =
      (τ j).restrict (π ⁻¹' W i ∩ π ⁻¹' W j)) :
    let μ := glued (fun i => π ⁻¹' W i) τ
    IsLocallyFiniteMeasure μ ∧ ∀ K : Set M, IsCompact K → μ (π ⁻¹' K) < ⊤ := by
  intro μ
  let U (i : ℕ) := π ⁻¹' W i
  let O (i : ℕ) := π ⁻¹' V i
  have hCoverW : ⋃ i, W i = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨i, hi⟩ := mem_iUnion.mp (cover.symm ▸ mem_univ x)
    exact mem_iUnion.mpr ⟨i, hSub i hi⟩
  have hCoverU : ⋃ i, U i = univ := by
    change ⋃ i, π ⁻¹' W i = univ
    rw [← preimage_iUnion, hCoverW, preimage_univ]
  have hLocal (i : ℕ) : μ (U i) = τ i (U i) := by
    have h := congrArg (fun m : Measure X => m univ) (glued_restrict U hW hCoverU τ hCompat i)
    simpa only [Measure.restrict_apply_univ] using h
  have hOfinite (i : ℕ) : μ (O i) < ⊤ := by
    calc
      μ (O i) ≤ μ (U i) := measure_mono (preimage_mono (hSub i))
      _ = τ i (U i) := hLocal i
      _ < ⊤ := hFinite i
  refine ⟨⟨fun x => ?_⟩, ?_⟩
  · obtain ⟨i, hi⟩ := mem_iUnion.mp (cover.symm ▸ mem_univ (π x))
    exact ⟨O i, ((hV i).preimage hπ).mem_nhds hi, hOfinite i⟩
  · intro K hK
    obtain ⟨I, hI⟩ := hK.elim_finite_subcover V hV (fun x _ => cover.symm ▸ mem_univ x)
    have hPre : π ⁻¹' K ⊆ ⋃ i ∈ I, O i := by
      intro p hp
      obtain ⟨i, hi, hp'⟩ := mem_iUnion₂.mp (hI hp)
      exact mem_iUnion₂.mpr ⟨i, hi, hp'⟩
    exact ((measure_mono hPre).trans (measure_biUnion_finset_le I O)).trans_lt
      (ENNReal.sum_lt_top.mpr fun i _ => hOfinite i)

end Burnett.Geometry.MeasureGluing
