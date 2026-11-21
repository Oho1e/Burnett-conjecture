import Burnett.Analysis.PrincipalEnergy.Localization.UniformMatrixGluing
import Burnett.Analysis.PrincipalEnergy.Localization.FixedLatticeCutoffs

set_option autoImplicit false
set_option maxHeartbeats 6100000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open Function MeasureTheory Filter Set Metric Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate ContDiff NNReal

/-- The matrix commutator bound is independent of the compact support of
the input and test. The lattice subpartition is selected after both tests;
the constant is selected before them. -/
theorem exists_actualMatrixCommutator_global_compactPair_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hs : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hb : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : ι → SchwartzMap Space ℂ,
        (∀ i, HasCompactSupport (f i : Space → ℂ)) →
        (∀ i, HasCompactSupport (g i : Space → ℂ)) →
        ‖actualMatrixCommutatorPair a r f g‖ ≤
          C * (U + (L : ℝ)) * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
  classical
  obtain ⟨χ, hχ, hχReal, hχOne⟩ := exists_lattice_schwartz_plateau
  obtain ⟨β, hβSupp, hβReal, hβPos, hβFinite⟩ := exists_lattice_schwartz_subpartition
  obtain ⟨M, N, hM, hN, bound⟩ :=
    exists_actualMatrixCommutator_moving_finite_gluing_bound ha hs hb hSym χ hχ hχReal
  let D : ℕ := 17^4
  let S : ℝ := √(D : ℝ)
  have hS : 0 ≤ S := Real.sqrt_nonneg _
  refine ⟨M*S*S+N, by positivity, fun r L U hr hR hVal hDer f g hf hg => ?_⟩
  let K := (⋃ i, tsupport (f i : Space → ℂ)) ∪ (⋃ i, tsupport (g i : Space → ℂ))
  have hK : IsCompact K := (isCompact_iUnion hf).union (isCompact_iUnion hg)
  obtain ⟨s, hSub, hOne⟩ := hβFinite K hK
  let α (i : ↥s) := β i.val
  let center (e : ↥s × ↥s) : Space := latticeCenter e.1.val
  let near : Finset (↥s × ↥s) := Finset.univ.filter fun e => latticeNear e.1.val e.2.val
  let far : Finset (↥s × ↥s) := Finset.univ.filter fun e => ¬latticeNear e.1.val e.2.val
  have near_mem (e : ↥s × ↥s) : e ∈ near ↔ latticeNear e.1.val e.2.val := by simp [near]
  have far_mem (e : ↥s × ↥s) : e ∈ far ↔ ¬latticeNear e.1.val e.2.val := by simp [far]
  have hSplit : Disjoint near far :=
    Finset.disjoint_left.mpr fun e hn hf => (far_mem e).mp hf ((near_mem e).mp hn)
  have hAll : near ∪ far = Finset.univ := by
    ext e
    simp only [Finset.mem_union, near_mem, far_mem, Finset.mem_univ, iff_true]
    exact em _
  have hOut (i : ↥s) : (near.filter fun e => e.1 = i).card ≤ D := by
    refine (Finset.card_le_card_of_injOn (t := s.filter fun b => latticeNear i.val b)
      (fun e : ↥s × ↥s => e.2.val) ?_ ?_).trans (lattice_pair_degree s i.val)
    · intro e he
      obtain ⟨hn, hi⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨e.2.property, hi ▸ (near_mem e).mp hn⟩
    · intro e he e' he' h
      exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he').2.symm) (Subtype.ext h)
  have hIn (j : ↥s) : (near.filter fun e => e.2 = j).card ≤ D := by
    refine (Finset.card_le_card_of_injOn (t := s.filter fun b => latticeNear j.val b)
      (fun e : ↥s × ↥s => e.1.val) ?_ ?_).trans (lattice_pair_degree s j.val)
    · intro e he
      obtain ⟨hn, hj⟩ := Finset.mem_filter.mp he
      exact Finset.mem_filter.mpr ⟨e.1.property, hj ▸ latticeNear_symm ((near_mem e).mp hn)⟩
    · intro e he e' he' h
      exact Prod.ext (Subtype.ext h) ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp he').2.symm)
  have hSub' (x : Space) : (∑ i : ↥s, (α i x).re) ≤ 1 := by
    change (∑ i ∈ s.attach, (β i.val x).re) ≤ 1
    rw [Finset.sum_attach s (fun a => (β a x).re)]
    exact hSub x
  have hOne' (x : Space) (hx : x ∈ K) : (∑ i : ↥s, α i x) = 1 := by
    change (∑ i ∈ s.attach, β i.val x) = 1
    rw [Finset.sum_attach s (fun a => β a x)]
    exact hOne x hx
  have hPlateau (e : ↥s × ↥s) (he : e ∈ near) (x : Space)
      (hx : x ∈ tsupport (α e.1 : Space → ℂ) ∪ tsupport (α e.2 : Space → ℂ)) :
      translateSchwartz (-center e) χ x = 1 := by
    have hBall := lattice_pair_plateau ((near_mem e).mp he)
      ((union_subset_union (hβSupp e.1.val) (hβSupp e.2.val)) hx)
    rw [translateSchwartz_apply]
    apply hχOne
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_eq_add_neg, center] using hBall
  have hGap (e : ↥s × ↥s) (he : e ∈ far) (x y : Space) (hx : α e.1 x ≠ 0) (hy : α e.2 y ≠ 0) :
      1 ≤ ‖x-y‖ :=
    lattice_pair_separated ((far_mem e).mp he)
      (hβSupp e.1.val (subset_closure hx)) (hβSupp e.2.val (subset_closure hy))
  have hOneF (i : ι) (x : Space) (hx : f i x ≠ 0) : (∑ j : ↥s, α j x) = 1 :=
    hOne' x (mem_union_left _ (mem_iUnion.mpr ⟨i, subset_closure hx⟩))
  have hOneG (i : ι) (x : Space) (hx : g i x ≠ 0) : (∑ j : ↥s, α j x) = 1 :=
    hOne' x (mem_union_right _ (mem_iUnion.mpr ⟨i, subset_closure hx⟩))
  have hEstimate := bound near far hSplit hAll α center D D 1 zero_lt_one hOut hIn
    (fun i => hβReal i.val) (fun i => hβPos i.val) hSub' hPlateau hGap r L U hr hR hVal hDer f g hf hOneF hOneG
  have hA : M * (U + (L : ℝ)) * S * S + N * U ≤ (M * S * S + N) * (U + (L : ℝ)) := by
    calc
      _ ≤ M * (U + (L : ℝ)) * S * S + N * (U + (L : ℝ)) :=
        add_le_add_left (mul_le_mul_of_nonneg_left (le_add_of_nonneg_right L.coe_nonneg) hN) _
      _ = _ := by ring
  have hEstimate' : ‖actualMatrixCommutatorPair a r f g‖ ≤
      (M * (U + (L : ℝ)) * S * S + N * U) * matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
    simpa only [inv_one, mul_one] using hEstimate
  exact hEstimate'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hA (norm_nonneg _)) (norm_nonneg _))

end Burnett.Analysis.CarlesonEmbedding
