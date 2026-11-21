import Burnett.Analysis.PrincipalEnergy.Localization.FiniteMatrixNear
import Burnett.Analysis.PrincipalEnergy.Localization.ActualKernelSupport

set_option autoImplicit false
set_option maxHeartbeats 5500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Analysis.FirstOrderDyadic
open scoped NNReal ComplexConjugate ContDiff BigOperators

/-- The actual whole matrix pairing expands through the same finite cuts
on both fields, when their sum is one on each component's support. -/
theorem actualMatrixCommutatorPair_eq_sum_cutoffs {ι κ : Type*} [Fintype ι] [Fintype κ]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (hc : ∀ i j, Continuous (uncurry (a i j))) (r : SchwartzMap Space ℂ)
    (α : κ → SchwartzMap Space ℂ) (f g : ι → SchwartzMap Space ℂ)
    (hf : ∀ j x, f j x ≠ 0 → ∑ k, α k x = 1)
    (hg : ∀ i x, g i x ≠ 0 → ∑ k, α k x = 1) :
    actualMatrixCommutatorPair a r f g = ∑ e : κ × κ, actualMatrixCommutatorPair a r
      (fun j => scalarSchwartzProduct (α e.2) (f j))
      (fun i => scalarSchwartzProduct (α e.1) (g i)) := by
  let F (k : κ) (j : ι) := scalarSchwartzProduct (α k) (f j)
  let G (k : κ) (i : ι) := scalarSchwartzProduct (α k) (g i)
  have hEntry (i j : ι) : actualScalarCommutatorPair (a i j) r (f j) (g i) =
      ∑ e : κ × κ, actualScalarCommutatorPair (a i j) r (F e.2 j) (G e.1 i) := by
    rw [← actualScalarCommutatorPair_sum_sum (ha i j) (hc i j) r (fun k => F k j) (fun k => G k i),
      sum_scalarSchwartzProduct_eq α (f j) (hf j), sum_scalarSchwartzProduct_eq α (g i) (hg i)]
  change actualMatrixCommutatorPair a r f g =
    ∑ e : κ × κ, actualMatrixCommutatorPair a r (F e.2) (G e.1)
  simp_rw [actualMatrixCommutatorPair_eq_sum_entries ha hc r]
  simp_rw [hEntry]
  calc
    _ = ∑ i, ∑ e : κ × κ, ∑ j, actualScalarCommutatorPair (a i j) r (F e.2 j) (G e.1 i) :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- All separated cutoff pairs of the original matrix operator are bounded
at once, with a constant fixed before the number and choice of patches. -/
theorem exists_actualFarMatrixCutoffPair_norm_le {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hc : ∀ i j, Continuous (uncurry (a i j))) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {κ : Type*} [Fintype κ] (far : Finset (κ × κ)) (α : κ → SchwartzMap Space ℂ),
        (∀ i x, α i x = ((α i x).re : ℂ)) → (∀ i x, 0 ≤ (α i x).re) →
        (∀ x, ∑ i, (α i x).re ≤ 1) → ∀ (d : ℝ), 0 < d →
        (∀ e ∈ far, ∀ x y, α e.1 x ≠ 0 → α e.2 y ≠ 0 → d ≤ ‖x-y‖) →
        ∀ (r : SchwartzMap Space ℂ) (f g : ι → SchwartzMap Space ℂ)
          (L : NNReal) (U : ℝ), LipschitzWith L r → 0 ≤ U → (∀ x, ‖r x‖ ≤ U) →
          (∀ j, HasCompactSupport (f j : Space → ℂ)) →
          ‖∑ e ∈ far, actualMatrixCommutatorPair a r
            (fun j => scalarSchwartzProduct (α e.2) (f j))
            (fun i => scalarSchwartzProduct (α e.1) (g i))‖ ≤
            C * U * d⁻¹ * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
  classical
  choose C hC hBound using fun i j =>
    exists_actualSeparatedCutoffPair_norm_le (ha i j) (hc i j)
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hC i j, ?_⟩
  intro κ _ far α hReal hPos hSub d hd hGap r f g L U hLip hU hSup hf
  let F (k : κ) (j : ι) := scalarSchwartzProduct (α k) (f j)
  let G (k : κ) (i : ι) := scalarSchwartzProduct (α k) (g i)
  let P (i j : ι) := ∑ e ∈ far, actualScalarCommutatorPair (a i j) r (F e.2 j) (G e.1 i)
  have hSum : (∑ e ∈ far, actualMatrixCommutatorPair a r (F e.2) (G e.1)) = ∑ i, ∑ j, P i j := by
    simp_rw [actualMatrixCommutatorPair_eq_sum_entries (fun i j => (ha i j).frequency) hc r, P]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm
  have hEntry (i j : ι) : ‖P i j‖ ≤
      C i j * U * d⁻¹ * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
    have hF : ‖(f j).toLp 2 volume‖ ≤ matrixSchwartzL2Norm f :=
      PiLp.norm_apply_le (WithLp.toLp 2 (fun k => (f k).toLp 2 volume)) j
    have hG : ‖(g i).toLp 2 volume‖ ≤ matrixSchwartzL2Norm g :=
      PiLp.norm_apply_le (WithLp.toLp 2 (fun k => (g k).toLp 2 volume)) i
    have hK : 0 ≤ C i j * U * d⁻¹ :=
      mul_nonneg (mul_nonneg (hC i j) hU) (inv_nonneg.mpr hd.le)
    have hFnonneg : 0 ≤ matrixSchwartzL2Norm f := by
      unfold matrixSchwartzL2Norm
      exact norm_nonneg _
    exact (hBound i j far α hReal hPos hSub d hd hGap r (f j) (g i) L U hLip hU hSup (hf j)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hF hK) hG
        (norm_nonneg _) (mul_nonneg hK hFnonneg))
  change ‖∑ e ∈ far, actualMatrixCommutatorPair a r (F e.2) (G e.1)‖ ≤ _
  rw [hSum]
  calc
    ‖∑ i, ∑ j, P i j‖ ≤ ∑ i, ‖∑ j, P i j‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖P i j‖ := Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, C i j * U * d⁻¹ * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hEntry i j
    _ = _ := by simp only [Finset.sum_mul]

/-- Entries outside both retained edge sets vanish on the actual cut
fields if their rectangle misses every genuine scalar kernel relation. -/
theorem actualMatrixCutoffPair_eq_zero_of_offKernelRelation {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hc : ∀ i j, Continuous (uncurry (a i j))) (α β : SchwartzMap Space ℂ)
    (r : SchwartzMap Space ℂ) (f g : ι → SchwartzMap Space ℂ) (L : NNReal) (U : ℝ)
    (hLip : LipschitzWith L r) (hSup : ∀ x, ‖r x‖ ≤ U)
    (hf : ∀ j, HasCompactSupport (f j : Space → ℂ))
    (hg : ∀ i, HasCompactSupport (g i : Space → ℂ))
    (hOff : ∀ i j, Disjoint (tsupport (α : Space → ℂ) ×ˢ tsupport (β : Space → ℂ))
      (firstOrderKernelRelation (a i j))) :
    actualMatrixCommutatorPair a r
      (fun j => scalarSchwartzProduct β (f j)) (fun i => scalarSchwartzProduct α (g i)) = 0 := by
  rw [actualMatrixCommutatorPair_eq_sum_entries (fun i j => (ha i j).frequency) hc r]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  apply actualScalarCommutatorPair_eq_zero_of_offKernelRelation (ha i j) (hc i j) _ _ _ L U hLip hSup
  · change HasCompactSupport (fun x => β x * f j x)
    exact (hf j).mul_left
  · change HasCompactSupport (fun x => α x * g i x)
    exact (hg i).mul_left
  · apply (hOff i j).mono_left
    exact Set.prod_mono tsupport_mul_subset_left tsupport_mul_subset_left

/-- A compact matrix input determines one compact test neighborhood for
the actual proper kernel relations of all its entries. -/
theorem exists_matrixCommutator_compact_test_region_of_properSupport {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hc : ∀ i j, Continuous (uncurry (a i j)))
    (hProper : ∀ i j, ProperKernelRelation (firstOrderKernelRelation (a i j)))
    (f : ι → SchwartzMap Space ℂ) (hf : ∀ j, HasCompactSupport (f j : Space → ℂ)) :
    ∃ K : Set Space, IsCompact K ∧
      ∀ (r : SchwartzMap Space ℂ) (g : ι → SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
        LipschitzWith L r → (∀ x, ‖r x‖ ≤ U) →
        (∀ i, HasCompactSupport (g i : Space → ℂ)) →
        (∀ i, Disjoint (tsupport (g i : Space → ℂ)) K) →
        actualMatrixCommutatorPair a r f g = 0 := by
  choose K hK hVanishing using fun i j =>
    exists_scalarCommutator_compact_test_region_of_properSupport (ha i j) (hc i j)
      (hProper i j) (f j) (hf j)
  refine ⟨⋃ i, ⋃ j, K i j, isCompact_iUnion (fun i => isCompact_iUnion (hK i)), ?_⟩
  intro r g L U hLip hSup hg hOff
  rw [actualMatrixCommutatorPair_eq_sum_entries (fun i j => (ha i j).frequency) hc r]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro j _
  have hSubset : K i j ⊆ ⋃ i, ⋃ j, K i j := Set.subset_iUnion₂ (s := K) i j
  exact hVanishing i j r (g i) L U hLip hSup (hg i) ((hOff i).mono_right hSubset)

end Burnett.Analysis.CarlesonEmbedding
