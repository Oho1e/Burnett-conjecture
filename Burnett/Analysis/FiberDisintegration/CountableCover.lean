import Mathlib.Probability.Kernel.Composition.MeasureCompProd

set_option autoImplicit false
noncomputable section

namespace Burnett.F08.FiberGluing

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]

/-- Use the first member of a measurable cover containing the base point.
The local kernels may have different mass bounds on different patches. -/
def patchKernel (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (k : ℕ → Kernel X Y) : Kernel X Y := by
  classical
  exact Kernel.sum fun n => Kernel.piecewise (MeasurableSet.disjointed hU n) (k n) 0

theorem patchKernel_apply (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (k : ℕ → Kernel X Y)
    (n : ℕ) {x : X} (hx : x ∈ disjointed U n) : patchKernel U hU k x = k n x := by
  classical
  ext s hs
  rw [patchKernel, Kernel.sum_apply' _ _ hs, tsum_eq_single n]
  · simp [Kernel.piecewise_apply', hx]
  · intro j hj
    have hno : x ∉ disjointed U j := fun hjx => (Set.disjoint_left.mp (disjoint_disjointed U hj)) hjx hx
    simp [Kernel.piecewise_apply', hno]

instance patchKernel_sFinite (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (k : ℕ → Kernel X Y) [∀ n, IsSFiniteKernel (k n)] : IsSFiniteKernel (patchKernel U hU k) := by
  classical
  unfold patchKernel
  infer_instance

theorem restrict_base_compProd (v : Measure X) [SFinite v] (k : Kernel X Y) [IsSFiniteKernel k]
    (P : Set X) (hP : MeasurableSet P) :
    (v ⊗ₘ k).restrict (Prod.fst ⁻¹' P) = v.restrict P ⊗ₘ k := by
  ext s hs
  rw [Measure.restrict_apply hs, Measure.compProd_apply (hs.inter (measurable_fst hP)), Measure.compProd_apply hs,
    ← lintegral_indicator hP]
  apply lintegral_congr
  intro x
  by_cases hx : x ∈ P
  · rw [indicator_of_mem hx]
    congr 1
    ext y
    simp [hx]
  · rw [indicator_of_notMem hx]
    have he : Prod.mk x ⁻¹' (s ∩ Prod.fst ⁻¹' P) = ∅ := by
      ext y
      simp [hx]
    rw [he, measure_empty]

/-- Local disintegrations of one phase measure, each on an open or Borel
patch with its own finite kernel bound, assemble to the original measure. -/
theorem patchKernel_disintegrates (v : Measure X) [SFinite v] (ρ : Measure (X × Y))
    (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n)) (cover : ⋃ n, U n = univ)
    (k : ℕ → Kernel X Y) [∀ n, IsFiniteKernel (k n)]
    (hLocal : ∀ n, v.restrict (U n) ⊗ₘ k n = ρ.restrict (Prod.fst ⁻¹' U n)) :
    (v ⊗ₘ patchKernel U hU k = ρ) ∧ (∀ x, IsFiniteMeasure (patchKernel U hU k x)) := by
  classical
  let D := disjointed U
  have hD n : MeasurableSet (D n) := MeasurableSet.disjointed hU n
  have hsub n : D n ⊆ U n := disjointed_subset U n
  have hcover : (⋃ n, D n) = univ := by simpa only [D, iUnion_disjointed] using cover
  have hc : (⋃ n, Prod.fst ⁻¹' D n : Set (X × Y)) = univ := by
    rw [← Set.preimage_iUnion, hcover, preimage_univ]
  constructor
  · apply Measure.ext_of_iUnion_eq_univ hc
    intro n
    have hp := congrArg (fun m : Measure (X × Y) => m.restrict (Prod.fst ⁻¹' D n)) (hLocal n)
    dsimp only at hp
    rw [restrict_base_compProd (v.restrict (U n)) (k n) _ (hD n), Measure.restrict_restrict (hD n),
      inter_eq_left.mpr (hsub n), Measure.restrict_restrict (measurable_fst (hD n)),
      inter_eq_left.mpr (preimage_mono (hsub n))] at hp
    rw [restrict_base_compProd _ _ _ (hD n), ← hp]
    apply Measure.compProd_congr
    filter_upwards [ae_restrict_mem (hD n)] with x hx
    exact patchKernel_apply U hU k n hx
  · intro x
    have hx : x ∈ ⋃ n, D n := by rw [hcover]; exact mem_univ _
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    rw [patchKernel_apply U hU k n hn]
    infer_instance

/-- Almost-everywhere fiber statements pass from the local measures to
the pasted kernel. This applies for example to concentration and tensor moments. -/
theorem patchKernel_ae_of_local (v : Measure X) (U : ℕ → Set X) (hU : ∀ n, MeasurableSet (U n))
    (cover : ⋃ n, U n = univ) (k : ℕ → Kernel X Y) (Q : X → Measure Y → Prop)
    (hQ : ∀ n, ∀ᵐ x ∂v.restrict (U n), Q x (k n x)) :
    ∀ᵐ x ∂v, Q x (patchKernel U hU k x) := by
  classical
  let D := disjointed U
  have hcover : (⋃ n, D n) = univ := by simpa only [D, iUnion_disjointed] using cover
  have h (n : ℕ) : ∀ᵐ x ∂v.restrict (D n), Q x (patchKernel U hU k x) := by
    have localQ := ae_mono (Measure.restrict_mono (disjointed_subset U n) le_rfl) (hQ n)
    filter_upwards [localQ, ae_restrict_mem (MeasurableSet.disjointed hU n)] with x hx hxD
    rwa [patchKernel_apply U hU k n hxD]
  have hUnion := (ae_restrict_iUnion_iff D (fun x => Q x (patchKernel U hU k x))).mpr h
  simpa only [hcover, Measure.restrict_univ] using hUnion

end Burnett.F08.FiberGluing
