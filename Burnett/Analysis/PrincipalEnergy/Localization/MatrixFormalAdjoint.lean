import Burnett.Analysis.PrincipalEnergy.Localization.SymbolLinearCombination

set_option autoImplicit false
set_option maxHeartbeats 2800000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Filter Function Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped BigOperators ComplexConjugate

/-- The actual action of finite matrix left quantization. -/
def matrixFirstOrderAction {ι : Type*} [Fintype ι]
    (a : ι → ι → Space → Space → ℂ) (f : ι → SchwartzMap Space ℂ)
    (i : ι) (x : Space) : ℂ :=
  ∑ j, firstOrderAction (a i j) (f j) x

/-- Symmetry of the matrix on the full common Schwartz domain and Lebesgue pairing. -/
def MatrixFirstOrderFormalSymmetry {ι : Type*} [Fintype ι]
    (a : ι → ι → Space → Space → ℂ) : Prop :=
  ∀ f g : ι → SchwartzMap Space ℂ,
    (∑ i, ∫ x, conj (g i x) * matrixFirstOrderAction a f i x) =
      ∑ i, ∫ x, conj (matrixFirstOrderAction a g i x) * f i x

/-- A test supported in one field component on each side extracts the
adjoint pair of entries from the single matrix symmetry assumption. -/
theorem matrixFirstOrderFormalSymmetry_entry_adjoint {ι : Type*} [Fintype ι]
    {a : ι → ι → Space → Space → ℂ} (ha : ∀ i j, FrequencyOrderOne (a i j))
    (hSym : MatrixFirstOrderFormalSymmetry a)
    (i j : ι) (u v : SchwartzMap Space ℂ) :
    (∫ x, conj (u x) * firstOrderAction (a i j) v x) =
      ∫ x, conj (firstOrderAction (a j i) u x) * v x := by
  classical
  let f (k : ι) := if k = j then v else 0
  let g (k : ι) := if k = i then u else 0
  have hZero (k l : ι) (x : Space) : firstOrderAction (a k l) (0 : SchwartzMap Space ℂ) x = 0 := by
    simpa only [smul_zero, sub_self, one_mul] using
      firstOrderAction_sub_smul (a k l) (ha k l) x (0 : SchwartzMap Space ℂ) 0 1
  have singleton (l k : ι) (w : SchwartzMap Space ℂ) (x : Space) :
      matrixFirstOrderAction a (fun b => if b = l then w else 0) k x =
        firstOrderAction (a k l) w x := by
    unfold matrixFirstOrderAction
    refine (Finset.sum_eq_single l (fun b _ hb => ?_) (fun h => (h (Finset.mem_univ l)).elim)).trans ?_
    · simp only [if_neg hb, hZero]
    · simp only [if_true]
  have hLeft :
      (∑ k, ∫ x, conj (g k x) * matrixFirstOrderAction a f k x) =
        ∫ x, conj (u x) * firstOrderAction (a i j) v x := by
    refine (Finset.sum_eq_single i (fun k _ hk => ?_) (fun h => (h (Finset.mem_univ i)).elim)).trans ?_
    · simp only [g, if_neg hk, SchwartzMap.zero_apply, map_zero, zero_mul, integral_zero]
    · simp only [g, if_pos rfl, f, singleton]
  have hRight :
      (∑ k, ∫ x, conj (matrixFirstOrderAction a g k x) * f k x) =
        ∫ x, conj (firstOrderAction (a j i) u x) * v x := by
    refine (Finset.sum_eq_single j (fun k _ hk => ?_) (fun h => (h (Finset.mem_univ j)).elim)).trans ?_
    · simp only [f, if_neg hk, SchwartzMap.zero_apply, mul_zero, integral_zero]
    · simp only [f, if_pos rfl, g, singleton]
  exact hLeft.symm.trans ((hSym f g).trans hRight)

private theorem integrable_actionPair_left {a : Space → Space → ℂ} (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (uncurry a)) (u v : SchwartzMap Space ℂ) :
    Integrable (fun x => conj (u x) * firstOrderAction a v x) :=
  (firstOrderAction_integrable_of_compactBase hBase hCont v).bdd_mul
    u.continuous.aestronglyMeasurable.star
    ⟨SchwartzMap.seminorm ℝ 0 0 u, fun x => by
      rw [Complex.norm_conj]
      exact SchwartzMap.norm_le_seminorm ℝ u x⟩

private theorem integrable_actionPair_right {a : Space → Space → ℂ} (hBase : CompactBaseOrderOne a)
    (hCont : Continuous (uncurry a)) (u v : SchwartzMap Space ℂ) :
    Integrable (fun x => conj (firstOrderAction a u x) * v x) := by
  have hA := firstOrderAction_integrable_of_compactBase hBase hCont u
  have hC : Integrable (fun x => conj (firstOrderAction a u x)) := hA.norm.mono'
    hA.aestronglyMeasurable.star (Eventually.of_forall fun x => (Complex.norm_conj _).le)
  simpa only [mul_comm (v _)] using hC.bdd_mul v.continuous.aestronglyMeasurable
    ⟨SchwartzMap.seminorm ℝ 0 0 v, fun x => SchwartzMap.norm_le_seminorm ℝ v x⟩

/-- The Hermitian combinations use the two actual entries, with conjugated
scalar coefficients. Their symmetry follows from the two paired adjoint identities. -/
theorem combineSymbols_formalSymmetry_of_adjointEntries {a b : Space → Space → ℂ}
    (ha : FrequencyOrderOne a) (hb : FrequencyOrderOne b)
    (hBaseA : CompactBaseOrderOne a) (hBaseB : CompactBaseOrderOne b)
    (hContA : Continuous (uncurry a)) (hContB : Continuous (uncurry b))
    (hab : ∀ u v : SchwartzMap Space ℂ, (∫ x, conj (u x) * firstOrderAction a v x) =
      ∫ x, conj (firstOrderAction b u x) * v x)
    (hba : ∀ u v : SchwartzMap Space ℂ, (∫ x, conj (u x) * firstOrderAction b v x) =
      ∫ x, conj (firstOrderAction a u x) * v x)
    (c : ℂ) : FirstOrderFormalSymmetry (combineSymbols c (conj c) a b) := by
  intro u v
  simp_rw [firstOrderAction_combineSymbols ha hb]
  have leftA := integrable_actionPair_left hBaseA hContA u v
  have leftB := integrable_actionPair_left hBaseB hContB u v
  have rightA := integrable_actionPair_right hBaseA hContA u v
  have rightB := integrable_actionPair_right hBaseB hContB u v
  calc
    _ = ∫ x, c * (conj (u x) * firstOrderAction a v x) +
        conj c * (conj (u x) * firstOrderAction b v x) := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    _ = c * (∫ x, conj (u x) * firstOrderAction a v x) +
        conj c * (∫ x, conj (u x) * firstOrderAction b v x) := by
      rw [integral_add (leftA.const_mul c) (leftB.const_mul (conj c)), integral_const_mul, integral_const_mul]
    _ = conj c * (∫ x, conj (firstOrderAction a u x) * v x) +
        c * (∫ x, conj (firstOrderAction b u x) * v x) := by
      rw [hab u v, hba u v, add_comm]
    _ = ∫ x, conj c * (conj (firstOrderAction a u x) * v x) +
        c * (conj (firstOrderAction b u x) * v x) := by
      rw [integral_add (rightA.const_mul (conj c)) (rightB.const_mul c), integral_const_mul, integral_const_mul]
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [map_add, map_mul, starRingEnd_self_apply]
      ring

end Burnett.Analysis.CarlesonEmbedding
