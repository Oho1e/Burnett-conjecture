import Burnett.Analysis.PrincipalEnergy.Localization.CutoffMatrixLocalBound

set_option autoImplicit false
set_option maxHeartbeats 4500000
noncomputable section

namespace Burnett.Analysis.CarlesonEmbedding

open MeasureTheory Function Filter Set Burnett.Fourier Burnett.Analysis.FirstOrderDyadic
open scoped NNReal ComplexConjugate ContDiff BigOperators

/-- Cauchy-Schwarz for an actual finite set of ordered pairs,
with a separate bound for each of the two fiber cardinalities. -/
theorem finitePairs_sum_mul_le_degree {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (S : Finset (ι × κ)) (A B : ℕ)
    (hA : ∀ i, (S.filter fun e => e.1 = i).card ≤ A)
    (hB : ∀ j, (S.filter fun e => e.2 = j).card ≤ B)
    (u : ι → ℝ) (v : κ → ℝ) :
    (∑ e ∈ S, u e.1 * v e.2) ≤
      √(A : ℝ) * √(B : ℝ) * √(∑ i, u i ^ 2) * √(∑ j, v j ^ 2) := by
  have first : (∑ e ∈ S, u e.1 ^ 2) ≤ (A : ℝ) * ∑ i, u i ^ 2 := by
    rw [← Finset.sum_fiberwise' S Prod.fst (fun i => u i ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hA i) (sq_nonneg _)
  have second : (∑ e ∈ S, v e.2 ^ 2) ≤ (B : ℝ) * ∑ j, v j ^ 2 := by
    rw [← Finset.sum_fiberwise' S Prod.snd (fun j => v j ^ 2), Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hB j) (sq_nonneg _)
  calc
    (∑ e ∈ S, u e.1 * v e.2) ≤ √(∑ e ∈ S, u e.1 ^ 2) * √(∑ e ∈ S, v e.2 ^ 2) :=
      Real.sum_mul_le_sqrt_mul_sqrt S (fun e => u e.1) (fun e => v e.2)
    _ ≤ √((A : ℝ) * ∑ i, u i ^ 2) * √((B : ℝ) * ∑ j, v j ^ 2) :=
      mul_le_mul (Real.sqrt_le_sqrt first) (Real.sqrt_le_sqrt second)
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := by rw [Real.sqrt_mul (Nat.cast_nonneg A), Real.sqrt_mul (Nat.cast_nonneg B)]; ring

private theorem schwartz_norm_toLp_sq (f : SchwartzMap Space ℂ) :
    ‖f.toLp 2 volume‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [l2_norm_sq_integral]
  exact integral_congr_ae ((f.coeFn_toLp 2 volume).fun_comp fun z => ‖z‖ ^ 2)

/-- Multiplication of a Schwartz input by a nonnegative real subpartition
contracts the sum of its squared Lebesgue L2 norms. -/
theorem scalarCutoff_sum_norm_sq_le {ι : Type*} [Fintype ι]
    (α : ι → SchwartzMap Space ℂ) (hReal : ∀ i x, α i x = ((α i x).re : ℂ))
    (hNonneg : ∀ i x, 0 ≤ (α i x).re)
    (hSum : ∀ x, ∑ i, (α i x).re ≤ 1) (f : SchwartzMap Space ℂ) :
    (∑ i, ‖(scalarSchwartzProduct (α i) f).toLp 2 volume‖ ^ 2) ≤ ‖f.toLp 2 volume‖ ^ 2 := by
  let F (i : ι) := scalarSchwartzProduct (α i) f
  have hInt (g : SchwartzMap Space ℂ) : Integrable (fun x => ‖g x‖ ^ 2) :=
    (g.memLp 2 volume).integrable_norm_pow (by decide : (2 : ℕ) ≠ 0)
  change (∑ i, ‖(F i).toLp 2 volume‖ ^ 2) ≤ _
  simp_rw [schwartz_norm_toLp_sq]
  rw [← integral_finset_sum Finset.univ (fun i _ => hInt (F i))]
  apply integral_mono (integrable_finset_sum Finset.univ (fun i _ => hInt (F i))) (hInt f)
  intro x
  have hLe (i : ι) : (α i x).re ≤ 1 :=
    (Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => hNonneg j x) (Finset.mem_univ i)).trans (hSum x)
  have hNorm (i : ι) : ‖α i x‖ = (α i x).re :=
    calc
      ‖α i x‖ = ‖((α i x).re : ℂ)‖ := congrArg norm (hReal i x)
      _ = (α i x).re := by rw [Complex.norm_real, Real.norm_of_nonneg (hNonneg i x)]
  calc
    (∑ i, ‖F i x‖ ^ 2) = (∑ i, (α i x).re ^ 2) * ‖f x‖ ^ 2 := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      simp only [F, scalarSchwartzProduct_apply, norm_mul, mul_pow, hNorm]
    _ ≤ 1 * ‖f x‖ ^ 2 := by
      refine mul_le_mul_of_nonneg_right (?_ : (∑ i, (α i x).re ^ 2) ≤ 1) (sq_nonneg _)
      refine (Finset.sum_le_sum fun i _ => ?_).trans (hSum x)
      exact (pow_two ((α i x).re)).le.trans
        (by simpa using mul_le_mul_of_nonneg_left (hLe i) (hNonneg i x))
    _ = _ := one_mul _

/-- The same cutoff partition contracts the matrix field energy with
the original Hilbert direct sum over field components. -/
theorem matrixCutoff_sum_norm_sq_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    (α : ι → SchwartzMap Space ℂ) (hReal : ∀ i x, α i x = ((α i x).re : ℂ))
    (hNonneg : ∀ i x, 0 ≤ (α i x).re)
    (hSum : ∀ x, ∑ i, (α i x).re ≤ 1) (f : κ → SchwartzMap Space ℂ) :
    (∑ i, ‖WithLp.toLp 2 (fun j => (scalarSchwartzProduct (α i) (f j)).toLp 2 volume)‖ ^ 2) ≤
      ‖WithLp.toLp 2 (fun j => (f j).toLp 2 volume)‖ ^ 2 := by
  simp only [PiLp.norm_sq_eq_of_L2]
  rw [Finset.sum_comm]
  exact Finset.sum_le_sum fun j _ => scalarCutoff_sum_norm_sq_le α hReal hNonneg hSum (f j)

end Burnett.Analysis.CarlesonEmbedding
