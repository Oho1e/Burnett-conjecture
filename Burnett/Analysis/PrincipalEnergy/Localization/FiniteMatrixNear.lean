import Burnett.Analysis.PrincipalEnergy.Localization.FiniteCutoffEnergy
import Burnett.Analysis.PrincipalEnergy.Localization.ActualPartitionPairs

set_option autoImplicit false
set_option maxHeartbeats 5000000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Set Function Burnett.Analysis.FirstOrderDyadic
open scoped NNReal ComplexConjugate ContDiff BigOperators

/-- Lebesgue L2 norm of a matrix field, using the Hilbert sum over its components. -/
def matrixSchwartzL2Norm {ι : Type*} [Fintype ι] (f : ι → SchwartzMap Space ℂ) : ℝ :=
  ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖

/-- The actual matrix coefficient commutator paired with an actual vector test. -/
def actualMatrixCommutatorPair {ι : Type*} [Fintype ι] (a : ι → ι → Space → Space → ℂ)
    (r : SchwartzMap Space ℂ) (f g : ι → SchwartzMap Space ℂ) : ℂ :=
  ∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator a r f i x

theorem actualMatrixCommutatorPair_eq_sum_entries {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (hc : ∀ i j, Continuous (uncurry (a i j))) (r : SchwartzMap Space ℂ)
    (f g : ι → SchwartzMap Space ℂ) :
    actualMatrixCommutatorPair a r f g = ∑ i, ∑ j, actualScalarCommutatorPair (a i j) r (f j) (g i) := by
  unfold actualMatrixCommutatorPair
  apply Finset.sum_congr rfl
  intro i _
  simp only [matrixCoefficientCommutator_apply, Finset.mul_sum, actualScalarCommutatorPair]
  exact integral_finset_sum _ (fun j _ => integrable_actualScalarCommutatorPair (ha i j) (hc i j) r (f j) (g i))

/-- Finite near pairs are each estimated on a common real compact plateau.
Their combined bound uses the largest local constant and the two degrees,
together with one global L2 norm for each original field. -/
theorem exists_actualNearMatrixCutoffPair_norm_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ] {a : ι → ι → Space → Space → ℂ}
    (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hSmooth : ∀ i j, ContDiff ℝ ∞ (uncurry (a i j)))
    (hPure : ∀ i j (n : ℕ), ∃ C : ℝ, 0 ≤ C ∧ ∀ x ξ,
      ‖iteratedFDeriv ℝ n (fun y => a i j y ξ) x‖ ≤ C * (1 + ‖ξ‖))
    (hSym : MatrixFirstOrderFormalSymmetry a)
    (near : Finset (κ × κ)) (A B : ℕ)
    (hA : ∀ i, (near.filter fun e => e.1 = i).card ≤ A)
    (hB : ∀ j, (near.filter fun e => e.2 = j).card ≤ B)
    (α : κ → SchwartzMap Space ℂ) (χ : κ × κ → SchwartzMap Space ℂ)
    (hReal : ∀ i x, α i x = ((α i x).re : ℂ)) (hPositive : ∀ i x, 0 ≤ (α i x).re)
    (hSubpartition : ∀ x, ∑ i, (α i x).re ≤ 1)
    (hCompactχ : ∀ e, HasCompactSupport (χ e : Space → ℂ))
    (hRealχ : ∀ e x, conj (χ e x) = χ e x)
    (hPlateau : ∀ e ∈ near, ∀ x,
      x ∈ tsupport (α e.1 : Space → ℂ) ∪ tsupport (α e.2 : Space → ℂ) → χ e x = 1) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : ι → SchwartzMap Space ℂ,
        ‖∑ e ∈ near, actualMatrixCommutatorPair a r
          (fun j => scalarSchwartzProduct (α e.2) (f j))
          (fun i => scalarSchwartzProduct (α e.1) (g i))‖ ≤
          M * (U + (L : ℝ)) * √(A : ℝ) * √(B : ℝ) *
            matrixSchwartzL2Norm f * matrixSchwartzL2Norm g := by
  classical
  choose C hC hBound using fun e : κ × κ =>
    exists_matrix_coefficientCommutator_L2_pair_bound_for_fixed_cutoff ha hSmooth hPure hSym
      (χ e) (hCompactχ e) (hRealχ e)
  let MC : ℝ≥0 := near.sup (fun e => ⟨C e, hC e⟩)
  refine ⟨MC, MC.coe_nonneg, ?_⟩
  intro r L U hU hr hRr hAev hAed f g
  let F (k : κ) (j : ι) := scalarSchwartzProduct (α k) (f j)
  let G (k : κ) (i : ι) := scalarSchwartzProduct (α k) (g i)
  let T := fun e : κ × κ => actualMatrixCommutatorPair a r (F e.2) (G e.1)
  let M : ℝ := MC * (U + (L : ℝ))
  have hM : 0 ≤ M := mul_nonneg MC.coe_nonneg (add_nonneg hU L.coe_nonneg)
  have hEntry (e : κ × κ) (he : e ∈ near) :
      ‖T e‖ ≤ M * (matrixSchwartzL2Norm (G e.1) * matrixSchwartzL2Norm (F e.2)) := by
    have hf (j : ι) (x : Space) (hx : x ∈ tsupport (F e.2 j : Space → ℂ)) : χ e x = 1 :=
      hPlateau e he x (Set.mem_union_right _ (tsupport_mul_subset_left hx))
    have hg (i : ι) (x : Space) (hx : x ∈ tsupport (G e.1 i : Space → ℂ)) : χ e x = 1 :=
      hPlateau e he x (Set.mem_union_left _ (tsupport_mul_subset_left hx))
    have hCe : C e ≤ (MC : ℝ) := by
      exact_mod_cast (Finset.le_sup (f := fun e => (⟨C e, hC e⟩ : ℝ≥0)) he)
    calc
      ‖T e‖ ≤ C e * (U + (L : ℝ)) * matrixSchwartzL2Norm (F e.2) * matrixSchwartzL2Norm (G e.1) :=
        hBound e r L U hU hr hRr hAev hAed (F e.2) (G e.1) hf hg
      _ ≤ (MC : ℝ) * (U + (L : ℝ)) * matrixSchwartzL2Norm (F e.2) * matrixSchwartzL2Norm (G e.1) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCe (add_nonneg hU L.coe_nonneg))
            (norm_nonneg _)) (norm_nonneg _)
      _ = _ := by dsimp only [M]; ring
  have hF : √(∑ j, matrixSchwartzL2Norm (F j) ^ 2) ≤ matrixSchwartzL2Norm f := by
    refine (Real.sqrt_le_sqrt (matrixCutoff_sum_norm_sq_le α hReal hPositive hSubpartition f)).trans_eq ?_
    exact Real.sqrt_sq (norm_nonneg _)
  have hG : √(∑ i, matrixSchwartzL2Norm (G i) ^ 2) ≤ matrixSchwartzL2Norm g := by
    refine (Real.sqrt_le_sqrt (matrixCutoff_sum_norm_sq_le α hReal hPositive hSubpartition g)).trans_eq ?_
    exact Real.sqrt_sq (norm_nonneg _)
  have hAB : 0 ≤ √(A : ℝ) * √(B : ℝ) := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change ‖∑ e ∈ near, T e‖ ≤ _
  calc
    ‖∑ e ∈ near, T e‖ ≤ ∑ e ∈ near, ‖T e‖ := norm_sum_le _ _
    _ ≤ ∑ e ∈ near, M * (matrixSchwartzL2Norm (G e.1) * matrixSchwartzL2Norm (F e.2)) :=
      Finset.sum_le_sum hEntry
    _ = M * ∑ e ∈ near, matrixSchwartzL2Norm (G e.1) * matrixSchwartzL2Norm (F e.2) := by rw [Finset.mul_sum]
    _ ≤ M * (√(A : ℝ) * √(B : ℝ) *
        √(∑ i, matrixSchwartzL2Norm (G i) ^ 2) *
        √(∑ j, matrixSchwartzL2Norm (F j) ^ 2)) :=
      mul_le_mul_of_nonneg_left
        (finitePairs_sum_mul_le_degree near A B hA hB
          (fun i => matrixSchwartzL2Norm (G i)) (fun j => matrixSchwartzL2Norm (F j))) hM
    _ ≤ M * (√(A : ℝ) * √(B : ℝ) * matrixSchwartzL2Norm g * matrixSchwartzL2Norm f) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (mul_le_mul_of_nonneg_left hG hAB) hF (Real.sqrt_nonneg _)
          (mul_nonneg hAB (norm_nonneg _))) hM
    _ = _ := by dsimp only [M]; ring

end Burnett.Analysis.CarlesonEmbedding
