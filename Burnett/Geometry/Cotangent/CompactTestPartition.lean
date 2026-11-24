import Burnett.Geometry.ManifoldMetric
import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! Finite smooth weights for testing tensors over a compact part of an open chart cover. -/

set_option autoImplicit false
noncomputable section

namespace Burnett.Geometry.CotangentTests

open Filter Set
open Burnett.Geometry.ConnectionDifference (CoordinateSpace)
open Burnett.Geometry.ManifoldMetric (Model)
open scoped Topology ContDiff Manifold

variable {M : Type*} [TopologicalSpace M] [ChartedSpace CoordinateSpace M] [IsManifold Model ∞ M]
  [T2Space M]

/-- A compact set has a finite smooth partition on an open neighbourhood, with each weight
compactly supported in one of the prescribed open sets. The chosen indices may repeat. -/
theorem exists_finite_smooth_cutoffs_on_compact {ι : Type*}
    (U : ι → Set M) (hU : ∀ i, IsOpen (U i)) {K : Set M} (hK : IsCompact K)
    (hcover : K ⊆ ⋃ i, U i) :
    ∃ (n : ℕ) (idx : Fin n → ι) (ρ : Fin n → M → ℝ) (V : Set M),
      IsOpen V ∧ K ⊆ V ∧
      (∀ k, ContMDiff Model 𝓘(ℝ) ∞ (ρ k) ∧ HasCompactSupport (ρ k) ∧
        tsupport (ρ k) ⊆ U (idx k) ∧ ∀ x, ρ k x ∈ Icc (0 : ℝ) 1) ∧
      ∀ x ∈ V, ∑ k, ρ k x = 1 := by
  classical
  have hlocal (x : K) : ∃ i : ι, ∃ b : SmoothBumpFunction Model x.1,
      tsupport b ⊆ U i := by
    obtain ⟨i, hx⟩ := mem_iUnion.mp (hcover x.prop)
    obtain ⟨b, _, hb⟩ := (SmoothBumpFunction.nhds_basis_tsupport (I := Model) x.1).mem_iff.mp
      ((hU i).mem_nhds hx)
    exact ⟨i, b, hb⟩
  choose label bump hsub using hlocal
  let O (x : K) := interior {y : M | bump x y = 1}
  have hcenter (x : K) : x.1 ∈ O x :=
    mem_interior_iff_mem_nhds.mpr (bump x).eventuallyEq_one
  obtain ⟨J, hJ⟩ := hK.elim_finite_subcover O (fun _ => isOpen_interior)
    (fun x hx => mem_iUnion.mpr ⟨⟨x, hx⟩, hcenter ⟨x, hx⟩⟩)
  let e := Fintype.equivFin (↑J : Type _)
  let pick (k : Fin (Fintype.card (↑J : Type _))) : K := (e.symm k).1
  let V := ⋃ k, O (pick k)
  have hKV : K ⊆ V := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := mem_iUnion₂.mp (hJ hx)
    refine mem_iUnion.mpr ⟨e ⟨a, ha⟩, ?_⟩
    simpa only [pick, e.symm_apply_apply] using hxa
  let B : SmoothBumpCovering (Fin (Fintype.card (↑J : Type _))) Model M V :=
    { c := fun k => (pick k).1
      toFun := fun k => bump (pick k)
      c_mem' := fun k => mem_iUnion.mpr ⟨k, hcenter (pick k)⟩
      locallyFinite' := locallyFinite_of_finite _
      eventuallyEq_one' := by
        intro x hx
        obtain ⟨k, hk⟩ := mem_iUnion.mp hx
        exact ⟨k, mem_interior_iff_mem_nhds.mp hk⟩ }
  let P := B.toSmoothPartitionOfUnity
  refine ⟨_, fun k => label (pick k), fun k => P k, V, isOpen_iUnion (fun _ => isOpen_interior),
    hKV, ?_, ?_⟩
  · intro k
    have hts : tsupport (P k) ⊆ tsupport (bump (pick k)) :=
      closure_mono (B.support_toSmoothPartitionOfUnity_subset k)
    exact ⟨(P k).contMDiff, (bump (pick k)).hasCompactSupport.of_isClosed_subset isClosed_closure hts,
      hts.trans (hsub (pick k)), fun x => ⟨P.nonneg k x, P.toPartitionOfUnity.le_one k x⟩⟩
  · intro x hx
    simpa only [finsum_eq_sum_of_fintype] using P.sum_eq_one hx

end Burnett.Geometry.CotangentTests
