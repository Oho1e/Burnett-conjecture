import Burnett.Analysis.PrincipalEnergy.Localization.MatrixFormalAdjoint

set_option autoImplicit false
set_option maxHeartbeats 3500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate NNReal

private theorem integrable_coefficientCommutatorPair {a : Space → Space → ℂ}
    (hBase : CompactBaseOrderOne a) (hCont : Continuous (uncurry a))
    (r f g : SchwartzMap Space ℂ) :
    Integrable (fun x => conj (g x) * actualCoefficientCommutator a r f x) :=
  (actualCoefficientCommutator_integrable hBase hCont r f).bdd_mul
    g.continuous.aestronglyMeasurable.star
    ⟨SchwartzMap.seminorm ℝ 0 0 g, fun x => by
      rw [Complex.norm_conj]
      exact SchwartzMap.norm_le_seminorm ℝ g x⟩

/-- An actual entry with a paired adjoint has the scalar commutator bound.
The two scalar applications use the Hermitian sum and the imaginary
Hermitian difference with the given adjoint entry. -/
theorem exists_compactBase_adjointEntry_coefficientCommutator_L2_pair_bound
    {a b : Space → Space → ℂ} (ha : FirstBaseFrequencyOrderOne a) (hb : FirstBaseFrequencyOrderOne b)
    (hBaseA : CompactBaseOrderOne a) (hBaseB : CompactBaseOrderOne b)
    (hContA : Continuous (uncurry a)) (hContB : Continuous (uncurry b))
    (hab : ∀ u v : SchwartzMap Space ℂ, (∫ x, conj (u x) * firstOrderAction a v x) =
      ∫ x, conj (firstOrderAction b u x) * v x)
    (hba : ∀ u v : SchwartzMap Space ℂ, (∫ x, conj (u x) * firstOrderAction b v x) =
      ∫ x, conj (firstOrderAction a u x) * v x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : SchwartzMap Space ℂ,
        ‖∫ x, conj (g x) * actualCoefficientCommutator a r f x‖ ≤
          C * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ := by
  let s := combineSymbols 1 (conj 1) a b
  let t := combineSymbols Complex.I (conj Complex.I) a b
  have continuousCombination (c d : ℂ) : Continuous (uncurry (combineSymbols c d a b)) :=
    (hContA.const_smul c).add (hContB.const_smul d)
  have hs := combineSymbols_firstBaseFrequencyOrderOne ha hb 1 (conj 1)
  have ht := combineSymbols_firstBaseFrequencyOrderOne ha hb Complex.I (conj Complex.I)
  have hBs := combineSymbols_compactBaseOrderOne hBaseA hBaseB 1 (conj 1)
  have hBt := combineSymbols_compactBaseOrderOne hBaseA hBaseB Complex.I (conj Complex.I)
  have hS := combineSymbols_formalSymmetry_of_adjointEntries ha.frequency hb.frequency
    hBaseA hBaseB hContA hContB hab hba 1
  have hT := combineSymbols_formalSymmetry_of_adjointEntries ha.frequency hb.frequency
    hBaseA hBaseB hContA hContB hab hba Complex.I
  obtain ⟨CS, hCS, boundS⟩ := exists_compactBase_coefficientCommutator_L2_pair_bound
    hs hBs (continuousCombination 1 (conj 1)) hS
  obtain ⟨CT, hCT, boundT⟩ := exists_compactBase_coefficientCommutator_L2_pair_bound
    ht hBt (continuousCombination Complex.I (conj Complex.I)) hT
  refine ⟨CS + CT, add_nonneg hCS hCT, ?_⟩
  intro r L U hr hReal hU hL f g
  let P (x : Space) := conj (g x) * actualCoefficientCommutator a r f x
  let Q (x : Space) := conj (g x) * actualCoefficientCommutator s r f x
  let R (x : Space) := conj (g x) * actualCoefficientCommutator t r f x
  have hPoint (x : Space) : 2 * actualCoefficientCommutator a r f x =
      actualCoefficientCommutator s r f x - Complex.I * actualCoefficientCommutator t r f x := by
    simp only [s, t, actualCoefficientCommutator_combineSymbols ha.frequency hb.frequency,
      map_one, one_mul, Complex.conj_I]
    linear_combination
      (actualCoefficientCommutator a r f x - actualCoefficientCommutator b r f x) * Complex.I_mul_I
  have hQ : Integrable Q := integrable_coefficientCommutatorPair hBs (continuousCombination 1 (conj 1)) r f g
  have hR : Integrable R :=
    integrable_coefficientCommutatorPair hBt (continuousCombination Complex.I (conj Complex.I)) r f g
  have pairEq : 2 * (∫ x, P x) = (∫ x, Q x) - Complex.I * (∫ x, R x) := by
    calc
      _ = ∫ x, 2 * P x := (integral_const_mul _ _).symm
      _ = ∫ x, Q x - Complex.I * R x := by
        apply integral_congr_ae
        filter_upwards with x
        calc
          _ = conj (g x) * (2 * actualCoefficientCommutator a r f x) := by dsimp only [P]; ring
          _ = _ := by rw [hPoint x]; dsimp only [Q, R]; ring
      _ = _ := by rw [integral_sub hQ (hR.const_mul Complex.I), integral_const_mul]
  change ‖∫ x, P x‖ ≤ _
  calc
    _ ≤ 2 * ‖∫ x, P x‖ := by linarith only [norm_nonneg (∫ x, P x)]
    _ = ‖2 * (∫ x, P x)‖ := by rw [norm_mul]; norm_num
    _ ≤ ‖∫ x, Q x‖ + ‖∫ x, R x‖ := by
      rw [pairEq]
      simpa only [norm_mul, Complex.norm_I, one_mul] using
        norm_sub_le (∫ x, Q x) (Complex.I * (∫ x, R x))
    _ ≤ CS * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ +
        CT * (U + (L : ℝ)) * ‖f.toLp 2 volume‖ * ‖g.toLp 2 volume‖ :=
      add_le_add (boundS r L U hr hReal hU hL f g) (boundT r L U hr hReal hU hL f g)
    _ = _ := by ring

/-- Exact scalar multiplication commutator of the original matrix action. -/
def matrixCoefficientCommutator {ι : Type*} [Fintype ι] (a : ι → ι → Space → Space → ℂ)
    (r : SchwartzMap Space ℂ) (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) : ℂ :=
  r x * matrixFirstOrderAction a f i x -
    matrixFirstOrderAction a (fun j => scalarSchwartzProduct r (f j)) i x

theorem matrixCoefficientCommutator_apply {ι : Type*} [Fintype ι]
    (a : ι → ι → Space → Space → ℂ) (r : SchwartzMap Space ℂ)
    (f : ι → SchwartzMap Space ℂ) (i : ι) (x : Space) :
    matrixCoefficientCommutator a r f i x =
      ∑ j, actualCoefficientCommutator (a i j) r (f j) x := by
  simp only [matrixCoefficientCommutator, matrixFirstOrderAction, actualCoefficientCommutator,
    Finset.mul_sum, Finset.sum_sub_distrib]

/-- The compact-base matrix Calderón pairing for a scalar real coefficient.
The matrix symmetry pairs the entries across their two slots. -/
theorem exists_compactBase_matrix_coefficientCommutator_L2_pair_bound {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FirstBaseFrequencyOrderOne (a i j))
    (hBase : ∀ i j, CompactBaseOrderOne (a i j)) (hCont : ∀ i j, Continuous (uncurry (a i j)))
    (hSym : MatrixFirstOrderFormalSymmetry a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (r : SchwartzMap Space ℂ) (L : NNReal) (U : ℝ),
      0 ≤ U → HasCompactSupport (r : Space → ℂ) → (∀ x, conj (r x) = r x) →
      (∀ᵐ x ∂(volume : Measure Space), ‖r x‖ ≤ U) →
      (∀ᵐ x ∂(volume : Measure Space), ‖fderiv ℝ (r : Space → ℂ) x‖ ≤ (L : ℝ)) →
      ∀ f g : ι → SchwartzMap Space ℂ,
        ‖∑ i, ∫ x, conj (g i x) * matrixCoefficientCommutator a r f i x‖ ≤
          C * (U + (L : ℝ)) * ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖ *
            ‖WithLp.toLp 2 (fun i => (g i).toLp 2 volume)‖ := by
  have each (i j : ι) := exists_compactBase_adjointEntry_coefficientCommutator_L2_pair_bound
    (ha i j) (ha j i) (hBase i j) (hBase j i) (hCont i j) (hCont j i)
    (matrixFirstOrderFormalSymmetry_entry_adjoint (fun k l => (ha k l).frequency) hSym i j)
    (matrixFirstOrderFormalSymmetry_entry_adjoint (fun k l => (ha k l).frequency) hSym j i)
  choose C hC bound using each
  refine ⟨∑ i, ∑ j, C i j, Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => hC i j)), ?_⟩
  intro r L U hU hr hReal hValue hDeriv f g
  let F := WithLp.toLp 2 (fun j => (f j).toLp 2 volume)
  let G := WithLp.toLp 2 (fun i => (g i).toLp 2 volume)
  let A (i j : ι) (x : Space) := conj (g i x) * actualCoefficientCommutator (a i j) r (f j) x
  let K (i j : ι) := C i j * (U + (L : ℝ))
  have row (i : ι) : (∫ x, conj (g i x) * matrixCoefficientCommutator a r f i x) =
      ∑ j, ∫ x, A i j x := by
    simp only [matrixCoefficientCommutator_apply, Finset.mul_sum]
    exact integral_finset_sum Finset.univ
      (fun j _ => integrable_coefficientCommutatorPair (hBase i j) (hCont i j) r (f j) (g i))
  have hEntry (i j : ι) : ‖∫ x, A i j x‖ ≤ K i j * ‖F‖ * ‖G‖ := by
    have hK : 0 ≤ K i j := mul_nonneg (hC i j) (add_nonneg hU L.coe_nonneg)
    have hF : ‖(f j).toLp 2 volume‖ ≤ ‖F‖ := PiLp.norm_apply_le F j
    have hG : ‖(g i).toLp 2 volume‖ ≤ ‖G‖ := PiLp.norm_apply_le G i
    exact (bound i j r L U hr hReal hValue hDeriv (f j) (g i)).trans
      (mul_le_mul (mul_le_mul_of_nonneg_left hF hK) hG (norm_nonneg _) (by positivity))
  simp_rw [row]
  change ‖∑ i, ∑ j, ∫ x, A i j x‖ ≤ (∑ i, ∑ j, C i j) * (U + (L : ℝ)) * ‖F‖ * ‖G‖
  calc
    _ ≤ ∑ i, ‖∑ j, ∫ x, A i j x‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖∫ x, A i j x‖ := Finset.sum_le_sum (fun i _ => norm_sum_le _ _)
    _ ≤ ∑ i, ∑ j, K i j * ‖F‖ * ‖G‖ := Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => hEntry i j))
    _ = _ := by simp only [K, Finset.sum_mul]

end Burnett.Analysis.CarlesonEmbedding
